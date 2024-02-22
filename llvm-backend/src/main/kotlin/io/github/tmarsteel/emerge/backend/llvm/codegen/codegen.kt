package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrArrayLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrBooleanLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIfExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIntegerLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNotReallyAnExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNullLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStringLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStructMemberAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableReferenceExpression
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.i1
import io.github.tmarsteel.emerge.backend.llvm.dsl.i16
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i64
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeS8ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.afterReferenceDropped
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word
import io.github.tmarsteel.emerge.backend.llvm.isCPointerPointed
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.tackState

internal sealed interface ExecutableResult {
    class Terminated(val termination: BasicBlockBuilder.Termination) : ExecutableResult
    object ImplicitUnit : ExecutableResult
    class Value(
        val value: LlvmValue<*>,
    ) : ExecutableResult
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitCode(
    code: IrExecutable,
): ExecutableResult {
    when (code) {
        is IrCodeChunk -> {
            code.components.asSequence()
                .take(code.components.size - 1)
                .forEach(::emitCode)

            return code.components.lastOrNull()?.let(::emitCode)
                ?: ExecutableResult.ImplicitUnit
        }
        is IrVariableDeclaration -> {
            val type = context.getReferenceSiteType(code.type)
            val stackAllocation = alloca(type)
            code.emitRead = {
                stackAllocation.dereference()
            }
            code.emitWrite = { newValue ->
                store(newValue, stackAllocation)
            }
            defer {
                stackAllocation.afterReferenceDropped(code.type)
            }
            return ExecutableResult.ImplicitUnit
        }
        is IrAssignmentStatement -> {
            val toAssign = emitExpressionCode(code.value)
            when (val localTarget = code.target) {
                is IrVariableReferenceExpression -> localTarget.variable.emitWrite!!(this, toAssign)
                is IrStructMemberAccessExpression -> store(toAssign, localTarget.getPointerToStructMember())
                is IrNullLiteralExpression,
                is IrIntegerLiteralExpression,
                is IrBooleanLiteralExpression,
                is IrStringLiteralExpression,
                is IrArrayLiteralExpression,
                is IrStaticDispatchFunctionInvocationExpression,
                is IrIfExpression,
                is IrNotReallyAnExpression -> throw CodeGenerationException("Cannot assign to a ${localTarget::class.simpleName}")
            }
            return ExecutableResult.ImplicitUnit
        }
        is IrReturnStatement -> {
            // TODO: unit return to unit declaration
            val toReturn = emitExpressionCode(code.value)
            return ExecutableResult.Terminated(ret(toReturn))
        }
        is IrExpression -> {
            emitExpressionCodeIgnoringResult(code)
            return ExecutableResult.ImplicitUnit
        }
    }
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCode(
    expression: IrExpression,
): LlvmValue<LlvmType> {
    return emitExpressionCodeInternal(expression, true)!!
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCodeIgnoringResult(
    expression: IrExpression,
): Unit {
    emitExpressionCodeInternal(expression, false)
}

private fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCodeInternal(
    expression: IrExpression,
    evaluationResultUsed: Boolean,
): LlvmValue<LlvmType>? {
    when (expression) {
        is IrStringLiteralExpression -> {
            val llvmStructWrapper = context.getAllocationSiteType(expression.evaluatesTo) as EmergeStructType
            val byteArrayPtr = expression.assureByteArrayConstantIn(context)
            val ctor = llvmStructWrapper.defaultConstructor.getInContext(context)
            return call(ctor, listOf(byteArrayPtr))
        }
        is IrStructMemberAccessExpression -> return expression.getPointerToStructMember().dereference()
        is IrStaticDispatchFunctionInvocationExpression -> {
            return call(expression.function.llvmRef!!, expression.arguments.map { emitExpressionCode(it) })
        }
        is IrVariableReferenceExpression -> return expression.variable.emitRead!!()
        is IrIntegerLiteralExpression -> return if (!evaluationResultUsed) null else when ((expression.evaluatesTo as IrSimpleType).baseType.fqn.toString()) {
            "emerge.core.Byte" -> context.i8(expression.value.byteValueExact())
            "emerge.core.UByte" -> context.i8(expression.value.shortValueExact().toUByte())
            "emerge.core.Short" -> context.i16(expression.value.shortValueExact())
            "emerge.core.UShort" -> context.i16(expression.value.intValueExact().toUShort())
            "emerge.core.Int" -> context.i32(expression.value.intValueExact())
            "emerge.core.UInt" -> context.i32(expression.value.longValueExact().toUInt())
            "emerge.core.Long" -> context.i64(expression.value.longValueExact())
            "emerge.core.ULong" -> context.i64(expression.value.toLong())
            "emerge.core.iword" -> context.word(expression.value.longValueExact())
            "emerge.core.uword" -> context.word(expression.value.toLong())
            else -> throw CodeGenerationException("Unsupported integer literal type ${expression.evaluatesTo}")
        }
        is IrBooleanLiteralExpression -> return if (evaluationResultUsed) context.i1(expression.value) else null
        is IrNullLiteralExpression -> return if (evaluationResultUsed) context.nullValue(context.getReferenceSiteType(expression.evaluatesTo)) else null
        is IrArrayLiteralExpression -> {
            val elementCount = context.word(expression.elements.size)
            val arrayType = context.getAllocationSiteType(expression.evaluatesTo) as EmergeArrayType<*>
            val arrayPtr = call(arrayType.constructorOfUndefEntries.getInContext(context), listOf(elementCount))
            expression.elements.forEachIndexed { index, elementExpr ->
                val elementValue = emitExpressionCode(elementExpr).reinterpretAs(arrayType.elementType)
                val slotPtr = getelementptr(arrayPtr)
                    .member { elements }
                    .index(context.word(index))
                    .get()
                store(elementValue, slotPtr)
            }

            return arrayPtr
        }
        is IrIfExpression -> {
            val condition = emitExpressionCode(expression.condition)
            check(condition.type === LlvmBooleanType)
            @Suppress("UNCHECKED_CAST")
            condition as LlvmValue<LlvmBooleanType>

            if (expression.elseBranch == null) {
                conditionalBranch(
                    condition = condition,
                    ifTrue = thenBranch@{
                        this@thenBranch.emitCode(expression.thenBranch)
                        concludeBranch()
                    }
                )
                return if (evaluationResultUsed) context.pointerToUnitInstance.dereference() else null
            }

            if (!evaluationResultUsed) {
                val elseBuilder: (BasicBlockBuilder.Branch<EmergeLlvmContext, LlvmType>.() -> BasicBlockBuilder.Termination) = elseBranch@{
                    this@elseBranch.emitCode(expression.elseBranch!!)
                    concludeBranch()
                }

                conditionalBranch(
                    condition = condition,
                    ifTrue = thenBranch@{
                        this@thenBranch.emitCode(expression.thenBranch)
                        concludeBranch()
                    },
                    ifFalse = elseBuilder.takeIf { expression.elseBranch != null },
                )
                return null
            }

            val valueHolder = alloca(context.getReferenceSiteType(expression.evaluatesTo))

            conditionalBranch(
                condition = condition,
                ifTrue = branchEmitter(expression.thenBranch, valueHolder),
                ifFalse = branchEmitter(expression.elseBranch!!, valueHolder),
            )
            return valueHolder.dereference()
        }
        is IrNotReallyAnExpression -> throw CodeGenerationException("Cannot emit expression evaluation code for an ${expression::class.simpleName}")
    }
}

private fun branchEmitter(
    branchCode: IrExecutable,
    valueStorage: LlvmValue<LlvmPointerType<LlvmType>>,
): BasicBlockBuilder.Branch<EmergeLlvmContext, LlvmType>.() -> BasicBlockBuilder.Termination {
    return {
        when (val branchResult = emitCode(branchCode)) {
            is ExecutableResult.ImplicitUnit -> {
                store(context.pointerToUnitInstance.dereference(), valueStorage)
                concludeBranch()
            }
            is ExecutableResult.Value -> {
                store(branchResult.value, valueStorage)
                concludeBranch()
            }
            is ExecutableResult.Terminated -> branchResult.termination
        }
    }
}

/**
 * for locals: loads from the alloca'd location
 * for globals: loads from the result of LLVM.LLVMAddGlobal
 * for parameters: result of LLVM.LLVMGetParam
 */
internal var IrVariableDeclaration.emitRead: (BasicBlockBuilder<EmergeLlvmContext, *>.() -> LlvmValue<LlvmType>)? by tackState { null }

/**
 * for locals: stores to the alloca'd location
 * for globals: stores to the result of LLVM.LLVMAddGlobal
 * for parameters: throws an exception
 */
internal var IrVariableDeclaration.emitWrite: (BasicBlockBuilder<EmergeLlvmContext, *>.(v: LlvmValue<LlvmType>) -> Unit)? by tackState { null }

internal var IrStringLiteralExpression.byteArrayGlobal: LlvmGlobal<EmergeArrayType<LlvmI8Type>>? by tackState { null }
internal fun IrStringLiteralExpression.assureByteArrayConstantIn(context: EmergeLlvmContext): LlvmGlobal<EmergeArrayType<LlvmI8Type>> {
    byteArrayGlobal?.let { return it }
    val constant = EmergeS8ArrayType.buildConstantIn(
        context,
        utf8Bytes.asList(),
        { context.i8(it) }
    )
    val untypedGlobal = context.addGlobal(constant, LlvmGlobal.ThreadLocalMode.SHARED)
    val global = LlvmGlobal(untypedGlobal.raw, EmergeS8ArrayType)
    byteArrayGlobal = global
    return global
}

context(BasicBlockBuilder<EmergeLlvmContext, LlvmType>)
private fun IrStructMemberAccessExpression.getPointerToStructMember(): LlvmValue<LlvmPointerType<LlvmType>> {
    val baseStructPtr = emitExpressionCode(this.base)
    check(baseStructPtr.type is LlvmPointerType<*>)

    if (member.isCPointerPointed) {
        return baseStructPtr as LlvmValue<LlvmPointerType<LlvmType>>
    }

    check(baseStructPtr.type.pointed is EmergeStructType)
    @Suppress("UNCHECKED_CAST")
    baseStructPtr as LlvmValue<LlvmPointerType<EmergeStructType>>

    return getelementptr(baseStructPtr)
        .member(this.member)
        .get()
}