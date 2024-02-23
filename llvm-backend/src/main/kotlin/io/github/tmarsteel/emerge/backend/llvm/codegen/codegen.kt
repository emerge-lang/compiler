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
import io.github.tmarsteel.emerge.backend.llvm.tackState

internal sealed interface ExecutableResult {
    object ImplicitUnit : ExecutableResult
}

internal sealed interface ExpressionResult<out T : LlvmType> : ExecutableResult {
    class Terminated(val termination: BasicBlockBuilder.Termination) : ExpressionResult<Nothing>
    class Value<T : LlvmType>(
        val value: LlvmValue<T>,
    ) : ExpressionResult<T>
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
            val toAssign = when (val assigneeResult = emitExpressionCode(code.value)) {
                is ExpressionResult.Value<*> -> assigneeResult.value
                is ExpressionResult.Terminated -> return assigneeResult
            }
            when (val localTarget = code.target) {
                is IrVariableReferenceExpression -> {
                    if (localTarget.isInitialized) {
                        localTarget.variable.emitRead!!(this).afterReferenceDropped(localTarget.evaluatesTo)
                    }
                    localTarget.variable.emitWrite!!(this, toAssign)
                    toAssign.afterReferenceCreated(code.value.evaluatesTo)
                }
                is IrStructMemberAccessExpression -> {
                    when (val memberPointerResult = localTarget.getPointerToStructMember()) {
                        is ExpressionResult.Terminated -> return memberPointerResult
                        is ExpressionResult.Value<LlvmPointerType<LlvmType>> -> {
                            memberPointerResult.value.afterReferenceDropped(localTarget.member.type)
                            store(toAssign, memberPointerResult.value)
                            toAssign.afterReferenceCreated(code.value.evaluatesTo)
                        }
                    }
                }
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
            val toReturn = when (val returneeResult = emitExpressionCode(code.value)) {
                is ExpressionResult.Value -> returneeResult.value
                is ExpressionResult.Terminated -> return returneeResult
            }
            toReturn.afterReferenceCreated(code.value.evaluatesTo)
            return ExpressionResult.Terminated(ret(toReturn))
        }
        is IrExpression -> {
            emitExpressionCodeIgnoringResult(code)
            return ExecutableResult.ImplicitUnit
        }
    }
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCode(
    expression: IrExpression,
): ExpressionResult<*> {
    return emitExpressionCodeInternal(expression, true)
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCodeIgnoringResult(
    expression: IrExpression,
) {
    val result = emitExpressionCodeInternal(expression, false)
    if (result is ExpressionResult.Value<*>) {
        result.value.afterReferenceDropped(expression.evaluatesTo)
    }
}

private fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCodeInternal(
    expression: IrExpression,
    evaluationResultUsed: Boolean,
): ExpressionResult<*> {
    when (expression) {
        is IrStringLiteralExpression -> {
            val llvmStructWrapper = context.getAllocationSiteType(expression.evaluatesTo) as EmergeStructType
            val byteArrayPtr = expression.assureByteArrayConstantIn(context)
            val ctor = context.registerIntrinsic(llvmStructWrapper.defaultConstructor)
            return ExpressionResult.Value(
                call(ctor, listOf(byteArrayPtr))
            )
        }
        is IrStructMemberAccessExpression -> return when (val memberPointeResult = expression.getPointerToStructMember()) {
            is ExpressionResult.Value<LlvmPointerType<LlvmType>> -> ExpressionResult.Value(memberPointeResult.value.dereference())
            is ExpressionResult.Terminated -> memberPointeResult
        }
        is IrStaticDispatchFunctionInvocationExpression -> {
            val arguments = expression.arguments.map {
                // if this is not a value, then the frontend fucked something up!
                (emitExpressionCode(it) as ExpressionResult.Value).value
            }
            return ExpressionResult.Value(
                call(expression.function.llvmRef!!, arguments)
            )
        }
        is IrVariableReferenceExpression -> return ExpressionResult.Value(expression.variable.emitRead!!())
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
                val elementValue = when (val elementExprResult = emitExpressionCode(elementExpr)) {
                    is ExpressionResult.Value -> elementExprResult.value.reinterpretAs(arrayType.elementType)
                    is ExpressionResult.Terminated -> return elementExprResult
                }
                val slotPtr = getelementptr(arrayPtr)
                    .member { elements }
                    .index(context.word(index))
                    .get()
                store(elementValue, slotPtr)
            }

            return ExpressionResult.Value(arrayPtr)
        }
        is IrIfExpression -> {
            val conditionValue = when (val conditionResult = emitExpressionCode(expression.condition)) {
                is ExpressionResult.Value -> conditionResult.value
                is ExpressionResult.Terminated -> return conditionResult
            }
            check(conditionValue.type === LlvmBooleanType)
            @Suppress("UNCHECKED_CAST")
            conditionValue as LlvmValue<LlvmBooleanType>

            if (expression.elseBranch == null) {
                check(!evaluationResultUsed) {
                    "Cannot use an if as an expression when it doesn't define an else branch"
                }
                conditionalBranch(
                    condition = conditionValue,
                    ifTrue = thenBranch@{
                        val branchResult = this@thenBranch.emitCode(expression.thenBranch)
                        (branchResult as? ExpressionResult.Terminated)?.termination ?: concludeBranch()
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
        is IrNotReallyAnExpression -> throw CodeGenerationException("Cannot emit expression evaluation code for an ${expression::class.simpleName}")
    }
}

private class BranchEmitter(
    val branchCode: IrExecutable,
    val valueStorage: LlvmValue<LlvmPointerType<LlvmType>>?,
) {
    lateinit var branchResult: ExecutableResult
        private set

    val generatorFn: BasicBlockBuilder.Branch<EmergeLlvmContext, LlvmType>.() -> BasicBlockBuilder.Termination = {
        val localBranchResult = emitCode(branchCode)
        branchResult = localBranchResult
        when (localBranchResult) {
            is ExecutableResult.ImplicitUnit -> {
                if (valueStorage != null) {
                    store(context.pointerToPointerToUnitInstance.dereference(), valueStorage)
                }
                concludeBranch()
            }
            is ExpressionResult.Value<*> -> {
                if (valueStorage != null) {
                    store(localBranchResult.value, valueStorage)
                }
                concludeBranch()
            }
            is ExpressionResult.Terminated -> localBranchResult.termination
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
private fun IrStructMemberAccessExpression.getPointerToStructMember(): ExpressionResult<LlvmPointerType<LlvmType>> {
    if (member.isCPointerPointed) {
        return emitExpressionCode(this.base) as ExpressionResult<LlvmPointerType<LlvmType>>
    }

    val baseStructPtr = when (val baseExprResult = emitExpressionCode(this.base)) {
        is ExpressionResult.Value<*> -> baseExprResult.value
        is ExpressionResult.Terminated -> return baseExprResult
    }
    check(baseStructPtr.type is LlvmPointerType<*>)

    check(baseStructPtr.type.pointed is EmergeStructType)
    @Suppress("UNCHECKED_CAST")
    baseStructPtr as LlvmValue<LlvmPointerType<EmergeStructType>>

    return ExpressionResult.Value(
        getelementptr(baseStructPtr)
            .member(this.member)
            .get()
    )
}