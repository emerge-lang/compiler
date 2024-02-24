package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrArrayLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrBooleanLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrDropReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIfExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIntegerLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNotReallyAnExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNullLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStringLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.api.ir.IrStructMemberAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
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
import io.github.tmarsteel.emerge.backend.llvm.indexed
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeS8ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeStructType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.afterReferenceCreated
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.afterReferenceDropped
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word
import io.github.tmarsteel.emerge.backend.llvm.isCPointerPointed
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.tackLateInitState
import io.github.tmarsteel.emerge.backend.llvm.tackState

internal sealed interface ExecutableResult {
    object ExecutionOngoing : ExecutableResult
}

internal sealed interface ExpressionResult : ExecutableResult {
    class Terminated(val termination: BasicBlockBuilder.Termination) : ExpressionResult
    class Value(val value: LlvmValue<*>) : ExpressionResult
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitCode(
    code: IrExecutable,
): ExecutableResult {
    when (code) {
        is IrCreateReferenceStatement -> {
            code.reference.llvmValue.afterReferenceCreated(code.reference.type)
            return ExecutableResult.ExecutionOngoing
        }
        is IrDropReferenceStatement -> {
            code.reference.llvmValue.afterReferenceDropped(code.reference.type)
            return ExecutableResult.ExecutionOngoing
        }
        is IrCreateTemporaryValue -> {
            val valueResult = emitExpressionCode(code.value)
            if (valueResult is ExpressionResult.Value) {
                code.llvmValue = valueResult.value
            }
            return ExecutableResult.ExecutionOngoing
        }
        is IrCodeChunk -> {
            code.components.asSequence()
                .take(code.components.size - 1)
                .forEach(::emitCode)

            return code.components.lastOrNull()?.let(::emitCode)
                ?: ExecutableResult.ExecutionOngoing
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
            return ExecutableResult.ExecutionOngoing
        }
        is IrAssignmentStatement -> {
            when (val localTarget = code.target) {
                is IrAssignmentStatement.Target.Variable -> {
                    localTarget.declaration.emitWrite!!(this, code.value.declaration.llvmValue)
                }
                is IrAssignmentStatement.Target.StructMember -> {
                    val memberPointer = getPointerToStructMember(localTarget.structValue.declaration.llvmValue, localTarget.member)
                    store(code.value.declaration.llvmValue, memberPointer)
                }
            }
            return ExecutableResult.ExecutionOngoing
        }
        is IrReturnStatement -> {
            // TODO: unit return to unit declaration
            return ExpressionResult.Terminated(ret(code.value.declaration.llvmValue))
        }
    }
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCode(
    expression: IrExpression,
): ExpressionResult {
    when (expression) {
        is IrStringLiteralExpression -> {
            val llvmStructWrapper = context.getAllocationSiteType(expression.evaluatesTo) as EmergeStructType
            val byteArrayPtr = expression.assureByteArrayConstantIn(context)
            val ctor = context.registerIntrinsic(llvmStructWrapper.defaultConstructor)
            val stringTemporary = call(ctor, listOf(byteArrayPtr))
            defer {
                stringTemporary.afterReferenceDropped(false)
            }
            return ExpressionResult.Value(stringTemporary)
        }
        is IrStructMemberAccessExpression -> {
            val memberPointer = getPointerToStructMember(
                expression.base.declaration.llvmValue,
                expression.member,
            )
            return ExpressionResult.Value(memberPointer.dereference())
        }
        is IrStaticDispatchFunctionInvocationExpression -> {
            return ExpressionResult.Value(
                call(
                    expression.function.llvmRef!!,
                    expression.arguments.map { it.declaration.llvmValue },
                )
            )
        }
        is IrVariableAccessExpression -> return ExpressionResult.Value(expression.variable.emitRead!!())
        is IrIntegerLiteralExpression -> return ExpressionResult.Value(when ((expression.evaluatesTo as IrSimpleType).baseType.fqn.toString()) {
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
        })
        is IrBooleanLiteralExpression -> return ExpressionResult.Value(context.i1(expression.value))
        is IrNullLiteralExpression -> return ExpressionResult.Value(context.nullValue(context.getReferenceSiteType(expression.evaluatesTo)))
        is IrArrayLiteralExpression -> {
            val elementCount = context.word(expression.elements.size)
            val arrayType = context.getAllocationSiteType(expression.evaluatesTo) as EmergeArrayType<*>
            val arrayPtr = call(context.registerIntrinsic(arrayType.constructorOfUndefEntries), listOf(elementCount))
            for ((index, elementExpr) in expression.elements.indexed()) {
                val slotPtr = getelementptr(arrayPtr)
                    .member { elements }
                    .index(context.word(index))
                    .get()
                store(elementExpr.declaration.llvmValue, slotPtr)
            }

            return ExpressionResult.Value(arrayPtr)
        }
        is IrIfExpression -> {
            val conditionValue = expression.condition.declaration.llvmValue
            check(conditionValue.type === LlvmBooleanType)
            @Suppress("UNCHECKED_CAST")
            conditionValue as LlvmValue<LlvmBooleanType>

            if (expression.elseBranch == null) {
                conditionalBranch(
                    condition = conditionValue,
                    ifTrue = thenBranch@{
                        this@thenBranch.emitCode(expression.thenBranch.code)
                        concludeBranch()
                    }
                )
                return ExpressionResult.Value(context.pointerToPointerToUnitInstance.dereference())
            }

            val valueHolder = alloca(context.getReferenceSiteType(expression.evaluatesTo))

            val thenEmitter = BranchEmitter(expression.thenBranch, valueHolder)
            val elseEmitter = BranchEmitter(expression.elseBranch!!, valueHolder)

            conditionalBranch(
                condition = conditionValue,
                ifTrue = thenEmitter.generatorFn,
                ifFalse = elseEmitter.generatorFn,
            )

            if (thenEmitter.branchResult is ExpressionResult.Terminated && elseEmitter.branchResult is ExpressionResult.Terminated) {
                return ExpressionResult.Terminated(unreachable().first)
            }

            return ExpressionResult.Value(valueHolder.dereference())
        }
        is IrImplicitEvaluationExpression -> {
            emitCode(expression.code)
            return ExpressionResult.Value(expression.implicitValue.declaration.llvmValue)
        }
        is IrNotReallyAnExpression -> throw CodeGenerationException("Cannot emit expression evaluation code for an ${expression::class.simpleName}")
    }
}

private class BranchEmitter(
    val branchCode: IrImplicitEvaluationExpression,
    val valueStorage: LlvmValue<LlvmPointerType<LlvmType>>?,
) {
    lateinit var branchResult: ExecutableResult
        private set

    val generatorFn: BasicBlockBuilder.Branch<EmergeLlvmContext, LlvmType>.() -> BasicBlockBuilder.Termination = {
        val localBranchResult = emitExpressionCode(branchCode)
        branchResult = localBranchResult
        when (localBranchResult) {
            is ExpressionResult.Value -> {
                if (valueStorage != null) {
                    store(localBranchResult.value, valueStorage)
                }
                concludeBranch()
            }
            is ExpressionResult.Terminated -> localBranchResult.termination
        }
    }
}

// TODO: move IR amendments to ir_amendments.kt

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

internal var IrCreateTemporaryValue.llvmValue: LlvmValue<LlvmType> by tackLateInitState()

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

private fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.getPointerToStructMember(
    structPointer: LlvmValue<*>,
    member: IrStruct.Member
): LlvmValue<LlvmPointerType<LlvmType>> {
    check(structPointer.type is LlvmPointerType<*>)
    @Suppress("UNCHECKED_CAST")
    structPointer as LlvmValue<LlvmPointerType<LlvmType>>

    if (member.isCPointerPointed) {
        return structPointer
    }

    check(structPointer.type.pointed is EmergeStructType)
    @Suppress("UNCHECKED_CAST")
    return getelementptr(structPointer as LlvmValue<LlvmPointerType<EmergeStructType>>)
        .member(member)
        .get()
}