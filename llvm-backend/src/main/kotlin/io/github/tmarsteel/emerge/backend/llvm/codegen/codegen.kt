package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrAllocateObjectExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrArrayLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrBooleanLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassMemberVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateStrongReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrDeallocateObjectStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrDropStrongReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrDynamicDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIfExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIntegerLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNotReallyAnExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNullLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrRegisterWeakReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStringLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrUnregisterWeakReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrUpdateSourceLocationStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer.Companion.requireNotAutoboxed
import io.github.tmarsteel.emerge.backend.llvm.autoboxer
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction.Companion.callIntrinsic
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
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeS8ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.afterReferenceCreated
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.afterReferenceDropped
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arraySize
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.getDynamicCallAddress
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.registerWeakReference
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.unregisterWeakReference
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.llvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmType
import io.github.tmarsteel.emerge.backend.llvm.signatureHashes
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
        is IrCreateStrongReferenceStatement -> {
            code.reference.llvmValue.afterReferenceCreated(code.reference.type)
            return ExecutableResult.ExecutionOngoing
        }
        is IrDropStrongReferenceStatement -> {
            code.reference.declaration.llvmValue.afterReferenceDropped(code.reference.type)
            return ExecutableResult.ExecutionOngoing
        }
        is IrRegisterWeakReferenceStatement -> {
            requireNotAutoboxed(code.referredObject, "registering weak references")
            callIntrinsic(registerWeakReference, listOf(
                getPointerToStructMember(code.referenceStoredIn.objectValue.declaration.llvmValue, code.referenceStoredIn.memberVariable),
                code.referredObject.declaration.llvmValue,
            ))
            return ExecutableResult.ExecutionOngoing
        }
        is IrUnregisterWeakReferenceStatement -> {
            requireNotAutoboxed(code.referredObject, "unregistering weak references")
            callIntrinsic(unregisterWeakReference, listOf(
                getPointerToStructMember(code.referenceStoredIn.objectValue.declaration.llvmValue, code.referenceStoredIn.memberVariable),
                code.referredObject.declaration.llvmValue,
            ))
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
            val resultAfterNonImplicitCode = code.components.asSequence()
                .take((code.components.size - 1).coerceAtLeast(0))
                .fold(ExecutableResult.ExecutionOngoing as ExecutableResult) { accResult, component ->
                    if (accResult !is ExpressionResult.Terminated) {
                        emitCode(component)
                    } else {
                        accResult
                    }
                }

            if (resultAfterNonImplicitCode is ExpressionResult.Terminated) {
                return resultAfterNonImplicitCode
            }

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
                is IrAssignmentStatement.Target.ClassMemberVariable -> {
                    // TODO: autoboxing
                    val memberPointer = getPointerToStructMember(localTarget.objectValue.declaration.llvmValue, localTarget.memberVariable)
                    store(code.value.declaration.llvmValue, memberPointer)
                }
            }
            return ExecutableResult.ExecutionOngoing
        }
        is IrReturnStatement -> {
            // TODO: unit return to unit declaration
            return ExpressionResult.Terminated(ret(code.value.declaration.llvmValue))
        }
        is IrDeallocateObjectStatement -> {
            // the reason boxes are not supported here because in the scope of IrDeallocateObjectStatement,
            // it is far too late to save the day. The self-parameter to the constructor will already get the wrong type
            // due to the boxing. Instead, the backend will ignore the destructor given by the frontend and just
            // insert its own, which calls free on its own terms and types
            requireNotAutoboxed(code.value, "deallocating")
            call(context.freeFunction, listOf(code.value.declaration.llvmValue))
            return ExecutableResult.ExecutionOngoing
        }
        is IrUpdateSourceLocationStatement -> {
            markSourceLocation(code.lineNumber, code.columnNumber)
            return ExecutableResult.ExecutionOngoing
        }
    }
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCode(
    expression: IrExpression,
): ExpressionResult {
    when (expression) {
        is IrStringLiteralExpression -> {
            val llvmStructWrapper = context.getAllocationSiteType(expression.evaluatesTo) as EmergeClassType
            val byteArrayPtr = expression.assureByteArrayConstantIn(context)
            val stringTemporary = call(llvmStructWrapper.constructor, listOf(byteArrayPtr))

            // super dirty hack: the frontend assumes string literals are constants/statics, but they aren't
            // the frontend also assumes it has to do refcounting here, because it's not aware we're invoking
            // a constructor here. So, to workaround for now .... until string literals can become actual constants
            val stringRefcountPtr = stringTemporary.anyValueBase().member { strongReferenceCount }.get()
            store(
                sub(stringRefcountPtr.dereference(), context.word(1)),
                stringRefcountPtr,
            )

            return ExpressionResult.Value(stringTemporary)
        }
        is IrClassMemberVariableAccessExpression -> {
            if ((expression.base.type as? IrParameterizedType)?.simpleType?.baseType?.canonicalName?.toString() == "emerge.core.Array") {
                if (expression.memberVariable.name == "size") {
                    return ExpressionResult.Value(
                        callIntrinsic(arraySize, listOf(expression.base.declaration.llvmValue))
                    )
                }
            }

            expression.base.type.autoboxer?.let { autoboxer ->
                if (autoboxer.isAccessingIntoTheBox(context, expression)) {
                    return ExpressionResult.Value(autoboxer.rewriteAccessIntoTheBox(expression))
                }
            }
            val memberPointer = getPointerToStructMember(
                expression.base.declaration.llvmValue,
                expression.memberVariable,
            )
            return ExpressionResult.Value(memberPointer.dereference())
        }
        is IrAllocateObjectExpression -> {
            expression.clazz.autoboxer?.let { autoboxer ->
                require(autoboxer !is Autoboxer.UserFacingUnboxed) { "Cannot allocate a valuetype on the heap (encountered ${expression.clazz})"}
            }
            return ExpressionResult.Value(
                expression.clazz.llvmType.allocateUninitializedDynamicObject(this),
            )
        }
        is IrStaticDispatchFunctionInvocationExpression -> {
            return ExpressionResult.Value(
                call(
                    expression.function.llvmRef!!,
                    expression.arguments.map { it.declaration.llvmValue },
                )
            )
        }
        is IrDynamicDispatchFunctionInvocationExpression -> {
            val targetAddr = callIntrinsic(getDynamicCallAddress, listOf(
                expression.dispatchOn.declaration.llvmValue,
                context.word(expression.function.signatureHashes.first()),
            ))
            val callResult = call(targetAddr, expression.function.llvmFunctionType, expression.arguments.map { it.declaration.llvmValue })
            return ExpressionResult.Value(callResult)
        }
        is IrVariableAccessExpression -> return ExpressionResult.Value(expression.variable.emitRead!!())
        is IrIntegerLiteralExpression -> return ExpressionResult.Value(when ((expression.evaluatesTo as IrSimpleType).baseType.canonicalName.toString()) {
            "emerge.core.S8" -> context.i8(expression.value.byteValueExact())
            "emerge.core.U8" -> context.i8(expression.value.shortValueExact().toUByte())
            "emerge.core.S16" -> context.i16(expression.value.shortValueExact())
            "emerge.core.U16" -> context.i16(expression.value.intValueExact().toUShort())
            "emerge.core.S32" -> context.i32(expression.value.intValueExact())
            "emerge.core.U32" -> context.i32(expression.value.longValueExact().toUInt())
            "emerge.core.S64" -> context.i64(expression.value.longValueExact())
            "emerge.core.U64" -> context.i64(expression.value.toLong())
            "emerge.core.IWord" -> context.word(expression.value.longValueExact())
            "emerge.core.UWord" -> context.word(expression.value.toLong())
            else -> throw CodeGenerationException("Unsupported integer literal type ${expression.evaluatesTo}")
        })
        is IrBooleanLiteralExpression -> return ExpressionResult.Value(context.i1(expression.value))
        is IrNullLiteralExpression -> return ExpressionResult.Value(context.nullValue(context.getReferenceSiteType(expression.evaluatesTo)))
        is IrArrayLiteralExpression -> {
            val elementCount = context.word(expression.elements.size)
            val arrayType = context.getAllocationSiteType(expression.evaluatesTo) as EmergeArrayType<*>
            val arrayPtr = callIntrinsic(arrayType.constructorOfUndefEntries, listOf(elementCount))
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
                return ExpressionResult.Terminated(unreachable())
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
    val untypedGlobal = context.addGlobal(constant, LlvmThreadLocalMode.NOT_THREAD_LOCAL)
    val global = LlvmGlobal(untypedGlobal.raw, EmergeS8ArrayType)
    byteArrayGlobal = global
    return global
}

private fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.getPointerToStructMember(
    structPointer: LlvmValue<*>,
    member: IrClass.MemberVariable
): LlvmValue<LlvmPointerType<LlvmType>> {
    check(structPointer.type is LlvmPointerType<*>)
    @Suppress("UNCHECKED_CAST")
    structPointer as LlvmValue<LlvmPointerType<LlvmType>>

    check(structPointer.type.pointed is EmergeClassType)
    @Suppress("UNCHECKED_CAST")
    return getelementptr(structPointer as LlvmValue<LlvmPointerType<EmergeClassType>>)
        .member(member)
        .get()
}