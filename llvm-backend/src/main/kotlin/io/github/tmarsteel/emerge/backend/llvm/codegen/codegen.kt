package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.GET_AT_INDEX_FN_NAME
import io.github.tmarsteel.emerge.backend.SET_AT_INDEX_FN_NAME
import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrAllocateObjectExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseTypeReflectionExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrBooleanLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrBreakStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCatchExceptionStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassFieldAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrConditionalBranch
import io.github.tmarsteel.emerge.backend.api.ir.IrContinueStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateStrongReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrDeallocateObjectStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrDropStrongReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrDynamicDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExpressionSideEffectsStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrIfExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIntegerLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrInterface
import io.github.tmarsteel.emerge.backend.api.ir.IrInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIsNullExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrLoop
import io.github.tmarsteel.emerge.backend.api.ir.IrMemberFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrNotReallyAnExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNullInitializedArrayExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNullLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNumericComparisonExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrRegisterWeakReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrStaticDispatchFunctionInvocationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStringLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrThrowStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrTryCatchExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance
import io.github.tmarsteel.emerge.backend.api.ir.IrUnregisterWeakReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrUpdateSourceLocationStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer.Companion.autoBoxOrUnbox
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer.Companion.requireNotAutoboxed
import io.github.tmarsteel.emerge.backend.llvm.IrSimpleTypeImpl
import io.github.tmarsteel.emerge.backend.llvm.StateTackDelegate
import io.github.tmarsteel.emerge.backend.llvm.allDistinctSupertypesExceptAny
import io.github.tmarsteel.emerge.backend.llvm.autoboxer
import io.github.tmarsteel.emerge.backend.llvm.baseBaseType
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction.Companion.callIntrinsic
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.PhiBucket
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i1
import io.github.tmarsteel.emerge.backend.llvm.dsl.i16
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i64
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.emitBreak
import io.github.tmarsteel.emerge.backend.llvm.emitContinue
import io.github.tmarsteel.emerge.backend.llvm.hasNothrowAbi
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeBoolArrayCopyFn
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeBooleanArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.abortOnException
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.fallibleFailure
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocated
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeI16ArrayCopyFn
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeI32ArrayCopyFn
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeI64ArrayCopyFn
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeI8ArrayCopyFn
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeReferenceArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeS16ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeS32ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeS64ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeS8ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeSWordArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeU16ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeU32ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeU64ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeU8ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeUWordArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordArrayCopyFn
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.PointerToAnyEmergeValue
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.TypeinfoType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.afterReferenceCreated
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.afterReferenceDropped
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arrayAbstractFallibleGet
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arrayAbstractFallibleSet
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arrayAbstractPanicSet
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arraySize
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.getDynamicCallAddress
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.registerWeakReference
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.unregisterWeakReference
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word
import io.github.tmarsteel.emerge.backend.llvm.isUnit
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
import io.github.tmarsteel.emerge.backend.llvm.llvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.llvmName
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.llvmType
import io.github.tmarsteel.emerge.backend.llvm.memberVariable
import io.github.tmarsteel.emerge.backend.llvm.signatureHashes
import io.github.tmarsteel.emerge.backend.llvm.tackLateInitState
import io.github.tmarsteel.emerge.backend.llvm.tackState
import io.github.tmarsteel.emerge.backend.llvm.typeinfoHolder
import io.github.tmarsteel.emerge.common.CanonicalElementName

internal sealed interface ExecutableResult {
    object ExecutionOngoing : ExecutableResult
}

internal sealed interface ExpressionResult : ExecutableResult {
    class Terminated(val termination: BasicBlockBuilder.Termination) : ExpressionResult
    class Value(val value: LlvmValue<*>) : ExpressionResult
}

/**
 * Is defined within the context of [IrTryCatchExpression.fallibleCode] providing the ability to
 * go to the [IrTryCatchExpression.catchpad] to the code in [IrInvocationExpression.landingpad]
 * through [IrCatchExceptionStatement]
 */
internal fun interface TryContext {
    /**
     * within a [IrInvocationExpression.landingpad], catches the exception and jumps to the handling code
     */
    fun jumpToCatchpad(exceptionPtr: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>): BasicBlockBuilder.Termination
}

/**
 * @param functionHasNothrowAbi see [hasNothrowAbi]
 */
internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitCode(
    code: IrExecutable,
    functionReturnType: IrType,
    functionHasNothrowAbi: Boolean,
    expressionResultUsed: Boolean,
    tryContext: TryContext?,
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
                getPointerToStructMember(code.referenceStoredIn.objectValue.declaration.llvmValue, code.referenceStoredIn.field),
                code.referredObject.declaration.llvmValue,
            ))
            return ExecutableResult.ExecutionOngoing
        }
        is IrUnregisterWeakReferenceStatement -> {
            requireNotAutoboxed(code.referredObject, "unregistering weak references")
            callIntrinsic(unregisterWeakReference, listOf(
                getPointerToStructMember(code.referenceStoredIn.objectValue.declaration.llvmValue, code.referenceStoredIn.field),
                code.referredObject.declaration.llvmValue,
            ))
            return ExecutableResult.ExecutionOngoing
        }
        is IrCreateTemporaryValue -> {
            val valueResult = emitExpressionCode(
                code.value,
                functionReturnType,
                functionHasNothrowAbi,
                expressionResultUsed = true,
                tryContext,
            )
            return when (valueResult) {
                is ExpressionResult.Terminated -> valueResult
                is ExpressionResult.Value -> {
                    code.llvmValue = autoBoxOrUnbox(valueResult.value, code.value.evaluatesTo, code.type)
                    ExecutableResult.ExecutionOngoing
                }
            }
        }
        is IrExpressionSideEffectsStatement -> {
            val expr = code.expression
            if (expr is IrImplicitEvaluationExpression) {
                return emitCode(
                    expr.code,
                    functionReturnType,
                    functionHasNothrowAbi,
                    expressionResultUsed = false,
                    tryContext,
                )
            } else {
                return emitExpressionCode(
                    expr,
                    functionReturnType,
                    functionHasNothrowAbi,
                    expressionResultUsed = false,
                    tryContext,
                )
            }
        }
        is IrCodeChunk -> {
            val resultAfterNonImplicitCode = code.components.asSequence()
                .take((code.components.size - 1).coerceAtLeast(0))
                .fold(ExecutableResult.ExecutionOngoing as ExecutableResult) { accResult, component ->
                    if (accResult !is ExpressionResult.Terminated) {
                        emitCode(
                            component,
                            functionReturnType,
                            functionHasNothrowAbi,
                            expressionResultUsed = false,
                            tryContext,
                        )
                    } else {
                        accResult
                    }
                }

            if (resultAfterNonImplicitCode is ExpressionResult.Terminated) {
                return resultAfterNonImplicitCode
            }

            return code.components.lastOrNull()?.let {
                emitCode(
                    it,
                    functionReturnType,
                    functionHasNothrowAbi,
                    expressionResultUsed,
                    tryContext,
                )
            }
                ?: ExecutableResult.ExecutionOngoing
        }
        is IrVariableDeclaration -> {
            val type = context.getReferenceSiteType(code.type)
            if (code.isSSA) {
                code.emitRead = {
                    throw CodeGenerationException("invalid IR - accessing SSA variable `${code.name}` before its assignment at ${currentDebugLocation()}")
                }
                code.emitWrite = { value ->
                    check(value.isLlvmAssignableTo(type)) {
                        "Cannot write a value of type ${value.type} into a variable of type $type"
                    }
                    code.emitRead = { value }
                    value.name = code.name
                }
            } else {
                val stackAllocation = alloca(
                    type,
                    forceEntryBlock = !code.isReAssignable,
                    code.name + "Ptr",
                )
                code.emitRead = {
                    stackAllocation.dereference(code.name)
                }
                code.emitWrite = { newValue ->
                    check(newValue.isLlvmAssignableTo(type)) {
                        "Cannot write a value of type ${newValue.type} into a variable of type $type"
                    }
                    store(newValue, stackAllocation)
                }
            }
            return ExecutableResult.ExecutionOngoing
        }
        is IrAssignmentStatement -> {
            val valueForAssignment: LlvmValue<*> = autoBoxOrUnbox(code.value, code.target.type)

            when (val localTarget = code.target) {
                is IrAssignmentStatement.Target.Variable -> {
                    localTarget.declaration.emitWrite!!(this, valueForAssignment)
                }
                is IrAssignmentStatement.Target.ClassField -> {
                    // TODO: autoboxing
                    val memberPointer = getPointerToStructMember(localTarget.objectValue.declaration.llvmValue, localTarget.field)
                    store(valueForAssignment, memberPointer)
                }
            }
            return ExecutableResult.ExecutionOngoing
        }
        is IrReturnStatement -> {
            val rawReturnValue = autoBoxOrUnbox(code.value, functionReturnType)
            val llvmValueToReturn = if (functionHasNothrowAbi) {
                rawReturnValue
            } else {
                val compoundReturnType = this@emitCode.llvmFunctionReturnType as EmergeFallibleCallResult<*>
                // if it's not a EmergeFallibleCallResult, something is seriously wrong; functionHasNothrowAbi shouldn't be true then
                if (compoundReturnType is EmergeFallibleCallResult.OfVoid) {
                    // returning from a Unit-returning function; no value, no exception
                    context.nullValue(PointerToAnyEmergeValue)
                } else {
                    compoundReturnType as EmergeFallibleCallResult.WithValue<LlvmType>
                    var compoundReturnValue = compoundReturnType.buildConstantIn(context) {
                        setNull(compoundReturnType.returnValue)
                        setNull(compoundReturnType.exceptionPtr)
                    } as LlvmValue<EmergeFallibleCallResult.WithValue<LlvmType>>
                    compoundReturnValue = insertValue(compoundReturnValue, rawReturnValue) { returnValue }
                    compoundReturnValue
                }
            }

            return ExpressionResult.Terminated(ret(llvmValueToReturn))
        }
        is IrThrowStatement -> {
            val exceptionPtr = code.throwable.declaration.llvmValue.reinterpretAs(PointerToAnyEmergeValue)
            if (tryContext != null) {
                // throw inside a try-catch, jump directly to catch
                if (functionHasNothrowAbi) {
                    // verify that the catch can even do something about the exception
                    code.throwable.type.findSimpleTypeBound().baseType.allDistinctSupertypesExceptAny
                        .filter { it.canonicalName.packageName == CanonicalElementName.Package(listOf("emerge", "core")) }
                        .filter { it.canonicalName.simpleName == "Error" }
                        .firstOrNull()
                        ?.let {
                            throw CodeGenerationException("illegal IR - throwing a subtype of error within a try-catch in a nothrow function")
                        }
                }
                return ExpressionResult.Terminated(tryContext.jumpToCatchpad(exceptionPtr))
            }

            if (functionHasNothrowAbi) {
                throw CodeGenerationException("${IrThrowStatement::class.simpleName} in a nothrow context!")
            }

            this as BasicBlockBuilder<EmergeLlvmContext, out EmergeFallibleCallResult<*>>
            return ExpressionResult.Terminated(fallibleFailure(exceptionPtr))
        }
        is IrCatchExceptionStatement -> {
            check(tryContext != null) {
                "illegal IR - ${IrCatchExceptionStatement::class.simpleName} with no landingpad context"
            }
            val exceptionReference = code.exceptionReference.declaration.llvmValue
            check(exceptionReference.type.isAssignableTo(PointerToAnyEmergeValue))
            return ExpressionResult.Terminated(tryContext.jumpToCatchpad(exceptionReference.reinterpretAs(PointerToAnyEmergeValue)))
        }
        is IrConditionalBranch -> {
            val conditionValue = code.condition.declaration.llvmValue
            check(conditionValue.type == LlvmBooleanType)
            @Suppress("UNCHECKED_CAST")
            conditionValue as LlvmValue<LlvmBooleanType>

            if (code.elseBranch == null) {
                conditionalBranch(
                    condition = conditionValue,
                    ifTrue = {
                        val thenBranchResult = emitCode(
                            code.thenBranch,
                            functionReturnType,
                            functionHasNothrowAbi,
                            expressionResultUsed = false,
                            tryContext,
                        )
                        (thenBranchResult as? ExpressionResult.Terminated)?.termination ?: concludeBranch()
                    }
                )
                return ExecutableResult.ExecutionOngoing
            }

            var thenTerminates = false
            var elseTerminates = false
            conditionalBranch(
                condition = conditionValue,
                ifTrue = {
                    val thenBranchResult = emitCode(
                        code.thenBranch,
                        functionReturnType,
                        functionHasNothrowAbi,
                        expressionResultUsed = false,
                        tryContext,
                    )
                    thenTerminates = thenBranchResult is ExpressionResult.Terminated
                    (thenBranchResult as? ExpressionResult.Terminated)?.termination ?: concludeBranch()
                },
                ifFalse = {
                    val elseBranchResult = emitCode(
                        code.elseBranch!!,
                        functionReturnType,
                        functionHasNothrowAbi,
                        expressionResultUsed = false,
                        tryContext,
                    )
                    elseTerminates = elseBranchResult is ExpressionResult.Terminated
                    (elseBranchResult as? ExpressionResult.Terminated)?.termination ?: concludeBranch()
                },
            )

            return if (thenTerminates && elseTerminates) {
                ExpressionResult.Terminated(unreachable())
            } else {
                ExecutableResult.ExecutionOngoing
            }
        }
        is IrLoop -> {
            loop {
                code.emitBreak = { this@loop.breakLoop() }
                code.emitContinue = { this@loop.loopContinue() }

                val bodyResult = emitCode(
                    code.body,
                    functionReturnType,
                    functionHasNothrowAbi,
                    false,
                    tryContext,
                )

                StateTackDelegate.reset(code, IrLoop::emitBreak)
                StateTackDelegate.reset(code, IrLoop::emitContinue)

                when (bodyResult) {
                    ExecutableResult.ExecutionOngoing,
                    is ExpressionResult.Value -> loopContinue()
                    is ExpressionResult.Terminated -> bodyResult.termination
                }
            }

            return ExecutableResult.ExecutionOngoing
        }
        is IrBreakStatement -> {
            return ExpressionResult.Terminated(code.fromLoop.emitBreak!!())
        }
        is IrContinueStatement -> {
            return ExpressionResult.Terminated(code.loop.emitContinue!!())
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

/**
 * @param functionHasNothrowAbi see [hasNothrowAbi]
 */
internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitExpressionCode(
    expression: IrExpression,
    functionReturnType: IrType,
    functionHasNothrowAbi: Boolean,
    expressionResultUsed: Boolean,
    tryContext: TryContext?,
): ExpressionResult {
    when (expression) {
        is IrStringLiteralExpression -> {
            return ExpressionResult.Value(
                context.emergeStringLiteral(expression.utf8Bytes)
            )
        }
        is IrClassFieldAccessExpression -> {
            if (expression.baseBaseType.canonicalName.toString() == "emerge.core.Array") {
                if (expression.memberVariable?.name == "size") {
                    val memberValue = callIntrinsic(arraySize, listOf(expression.base.declaration.llvmValue))
                    return ExpressionResult.Value(
                        autoBoxOrUnbox(memberValue, IrSimpleTypeImpl(context.rawUWordClazz, IrTypeMutability.IMMUTABLE, false), expression.evaluatesTo)
                    )
                }
            }

            expression.base.type.autoboxer?.let { autoboxer ->
                if (autoboxer.isAccessingIntoTheBox(context, expression)) {
                    val rewrittenValue = autoboxer.rewriteAccessIntoTheBox(expression)
                    return ExpressionResult.Value(rewrittenValue)
                }
            }
            val memberPointer = getPointerToStructMember(
                expression.base.declaration.llvmValue
                    .reinterpretAs(context.getReferenceSiteType(expression.base.type)),
                expression.field,
            )
            val memberValue = autoBoxOrUnbox(memberPointer.dereference(), expression.field.type, expression.evaluatesTo)
            return ExpressionResult.Value(memberValue)
        }
        is IrAllocateObjectExpression -> {
            expression.clazz.autoboxer?.let { autoboxer ->
                require(autoboxer !is Autoboxer.PrimitiveType) { "Cannot allocate a valuetype on the heap (encountered ${expression.clazz})"}
            }
            return ExpressionResult.Value(
                expression.clazz.llvmType.allocateUninitializedDynamicObject(this),
            )
        }
        is IrInvocationExpression -> {
            val callInstruction = when (expression) {
                is IrStaticDispatchFunctionInvocationExpression -> {
                    var overridenCallInstruction: LlvmValue<*>? = null
                    // optimized array accessors
                    if ((expression.function as? IrMemberFunction)?.ownerBaseType?.canonicalName?.toString() == "emerge.core.Array") {
                        val override = ArrayDispatchOverride.findFor(expression, context)
                        when (override) {
                            is ArrayDispatchOverride.InvokeVirtual -> {
                                val addr = callIntrinsic(
                                    getDynamicCallAddress, listOf(
                                        expression.arguments.first().declaration.llvmValue,
                                        context.word(override.hash),
                                    )
                                )
                                overridenCallInstruction = call(
                                    addr,
                                    override.fnType,
                                    expression.arguments.zip(expression.function.parameters)
                                        .map { (argument, parameter) -> autoBoxOrUnbox(argument, parameter.type) }
                                )
                            }

                            is ArrayDispatchOverride.InvokeIntrinsic -> {
                                // IMPORTANT! this deliberately doesn't box the arguments because that would box primitives
                                // in exactly a situation where that shouldn't happen.
                                overridenCallInstruction = call(
                                    context.registerIntrinsic(override.intrinsic),
                                    expression.arguments.map { it.declaration.llvmValue }
                                )
                            }
                            else -> {}
                        }
                    }

                    if (overridenCallInstruction != null) {
                        overridenCallInstruction
                    } else {
                        // general handling
                        val llvmFunction = expression.function.llvmRef
                            ?: throw CodeGenerationException(
                                "Missing implementation for ${expression.function.canonicalName}; mangled name: ${expression.function.llvmName}"
                            )
                        call(
                            llvmFunction,
                            expression.arguments.zip(expression.function.parameters)
                                .map { (argument, parameter) -> autoBoxOrUnbox(argument, parameter.type) },
                        )
                    }
                }

                is IrDynamicDispatchFunctionInvocationExpression -> {
                    val argumentsForInvocation = expression.arguments.zip(expression.function.parameters)
                        .map { (argument, parameter) -> autoBoxOrUnbox(argument, parameter.type) }

                    val targetAddr = callIntrinsic(
                        getDynamicCallAddress, listOf(
                            expression.dispatchOn.declaration.llvmValue,
                            context.word(expression.function.signatureHashes.first()),
                        )
                    )
                    call(targetAddr, expression.function.llvmFunctionType, argumentsForInvocation)
                }
            }

            if (callInstruction.type !is EmergeFallibleCallResult<*>) {
                if (expression.evaluatesTo.isUnit) {
                    return ExpressionResult.Value(context.pointerToUnitInstance)
                }

                return ExpressionResult.Value(callInstruction)
            }

            // not checking functionHasNothrowAbi here, because it will turn into a panic at runtime if it's a nothrow context

            @Suppress("UNCHECKED_CAST") // implied by !hasNothrowAbi
            val unwrappedReturnValue = (callInstruction as LlvmValue<EmergeFallibleCallResult<LlvmType>>).abortOnException { exceptionPtr ->
                if (expression.landingpad == null) {
                    return@abortOnException propagateOrPanic(exceptionPtr)
                }
                val invocationLandingpad = expression.landingpad!!
                invocationLandingpad.throwableVariable.emitRead = { exceptionPtr }
                invocationLandingpad.throwableVariable.emitWrite = {
                    throw CodeGenerationException("Cannot write to exception variables in landingpads or catchpads!")
                }
                val landingpadResult = emitCode(
                    invocationLandingpad.code,
                    functionReturnType,
                    functionHasNothrowAbi,
                    expressionResultUsed,
                    tryContext,
                )

                check(landingpadResult is ExpressionResult.Terminated) {
                    "illegal IR - landingpad does not terminate. It should either catch or rethrow"
                }
                landingpadResult.termination
            }

            if (expression.evaluatesTo.isUnit) {
                return ExpressionResult.Value(context.pointerToUnitInstance)
            }

            return ExpressionResult.Value(unwrappedReturnValue)
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
            "emerge.core.SWord" -> context.word(expression.value.longValueExact())
            "emerge.core.UWord" -> context.word(expression.value.toLong())
            else -> throw CodeGenerationException("Unsupported integer literal type ${expression.evaluatesTo}")
        })
        is IrBooleanLiteralExpression -> return ExpressionResult.Value(context.i1(expression.value))
        is IrNullLiteralExpression -> return ExpressionResult.Value(context.nullValue(context.getReferenceSiteType(expression.evaluatesTo)))
        is IrNullInitializedArrayExpression -> {
            val elementCount = context.word(expression.size)
            val arrayType = context.getAllocationSiteType(expression.evaluatesTo) as EmergeArrayType<*>
            val arrayPtr = callIntrinsic(arrayType.constructorOfNullEntries, listOf(elementCount))
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
                        val branchCodeResult = this@thenBranch.emitCode(
                            expression.thenBranch.code,
                            functionReturnType,
                            functionHasNothrowAbi,
                            expressionResultUsed = false,
                            tryContext,
                        )
                        (branchCodeResult as? ExpressionResult.Terminated)?.termination ?: concludeBranch()
                    }
                )
                return ExpressionResult.Value(context.pointerToUnitInstance)
            }

            val expressionResultLlvmType = context.getReferenceSiteType(expression.evaluatesTo)
            val valueBucket = if (expressionResultUsed) PhiBucket(expressionResultLlvmType) else null

            val thenEmitter = IfElseExprBranchEmitter(expression.thenBranch, valueBucket, expression.evaluatesTo, functionHasNothrowAbi, functionReturnType, tryContext)
            val elseEmitter = IfElseExprBranchEmitter(expression.elseBranch!!, valueBucket, expression.evaluatesTo, functionHasNothrowAbi, functionReturnType, tryContext)

            conditionalBranch(
                condition = conditionValue,
                ifTrue = thenEmitter.generatorFn,
                ifFalse = elseEmitter.generatorFn,
            )

            if (thenEmitter.branchResult is ExpressionResult.Terminated && elseEmitter.branchResult is ExpressionResult.Terminated) {
                return ExpressionResult.Terminated(unreachable())
            }

            return if (expressionResultUsed) {
                ExpressionResult.Value(valueBucket!!.buildPhi())
            } else {
                ExpressionResult.Value(context.poisonValue(expressionResultLlvmType))
            }
        }
        is IrNumericComparisonExpression -> {
            val operandType = expression.lhs.type.findSimpleTypeBound().baseType
            if (operandType.canonicalName.simpleName in setOf("F32", "F64")) {
                TODO("floating point comparison not implemented yet")
            }

            val isSigned = operandType.canonicalName.simpleName.startsWith('S')
            val llvmPredicate = when (expression.predicate) {
                IrNumericComparisonExpression.Predicate.GREATER_THAN -> if (isSigned) {
                    LlvmIntPredicate.SIGNED_GREATER_THAN
                } else {
                    LlvmIntPredicate.UNSIGNED_GREATER_THAN
                }
                IrNumericComparisonExpression.Predicate.GREATER_THAN_OR_EQUAL -> if (isSigned) {
                    LlvmIntPredicate.SIGNED_GREATER_THAN_OR_EQUAL
                } else {
                    LlvmIntPredicate.UNSIGNED_GREATER_THAN_OR_EQUAL
                }
                IrNumericComparisonExpression.Predicate.LESS_THAN -> if (isSigned) {
                    LlvmIntPredicate.SIGNED_LESS_THAN
                } else {
                    LlvmIntPredicate.UNSIGNED_LESS_THAN
                }
                IrNumericComparisonExpression.Predicate.LESS_THAN_OR_EQUAL -> if (isSigned) {
                    LlvmIntPredicate.SIGNED_LESS_THAN
                } else {
                    LlvmIntPredicate.UNSIGNED_LESS_THAN_OR_EQUAL
                }
                IrNumericComparisonExpression.Predicate.EQUAL -> LlvmIntPredicate.EQUAL
            }

            @Suppress("UNCHECKED_CAST")
            val lhsValue = expression.lhs.declaration.llvmValue as LlvmValue<LlvmIntegerType>
            @Suppress("UNCHECKED_CAST")
            val rhsValue = expression.rhs.declaration.llvmValue as LlvmValue<LlvmIntegerType>
            
            val result = icmp(lhsValue, llvmPredicate, rhsValue)
            return ExpressionResult.Value(result)
        }
        is IrIsNullExpression -> {
            if (!expression.nullableValue.type.isNullable) {
                return ExpressionResult.Value(context.i1(false))
            }

            // because the type is nullable, it is guaranteed that it is a boxed version of a possibly boxable type
            // hence it is guaranteed that nullableValue holds a pointer
            val llvmValue = expression.nullableValue.declaration.llvmValue
            check(llvmValue.type is LlvmPointerType<*>)
            @Suppress("UNCHECKED_CAST")
            llvmValue as LlvmValue<LlvmPointerType<*>>

            return ExpressionResult.Value(isNull(llvmValue))
        }
        is IrBaseTypeReflectionExpression -> {
            check(expression.evaluatesTo.autoboxer == Autoboxer.ReflectionBaseType)
            val boxedType = expression.baseType.autoboxer?.getBoxedType(context)
            val typeinfoPtr: LlvmValue<LlvmPointerType<TypeinfoType>> = when (boxedType) {
                null -> when (val localBaseType = expression.baseType) {
                    is IrClass -> {
                        val emergeClass = context.getEmergeClassByIrType(expression.baseType)
                            ?: throw CodeGenerationException("Cannot reflect on unknown base type ${expression.baseType}")
                        emergeClass.getTypeinfoInContext(context).dynamic
                    }
                    is IrInterface -> localBaseType.typeinfoHolder.getTypeinfoInContext(context)
                    else -> throw CodeGenerationException("Unsupported base type ${localBaseType::class.qualifiedName}")
                }
                else -> boxedType.getTypeinfoInContext(context).dynamic
            }

            return ExpressionResult.Value(typeinfoPtr)
        }
        is IrTryCatchExpression -> {
            val tryCatchResultLlvmType = context.getReferenceSiteType(expression.evaluatesTo, false)
            val resultBucket = if (expressionResultUsed) PhiBucket(tryCatchResultLlvmType) else null
            val exceptionBucket = PhiBucket(PointerToAnyEmergeValue)
            unsafeBranch(
                prepareBlockName = "try",
                prepare = {
                    val fallibleExprResult = emitExpressionCode(
                        expression.fallibleCode,
                        functionReturnType,
                        functionHasNothrowAbi,
                        expressionResultUsed,
                        tryContext = { exceptionPtr ->
                            exceptionBucket.setBranchResult(exceptionPtr)
                            jumpToUnsafeBranch()
                        }
                    )
                    when (fallibleExprResult) {
                        is ExpressionResult.Terminated -> fallibleExprResult.termination
                        is ExpressionResult.Value -> {
                            resultBucket?.setBranchResult(fallibleExprResult.value)
                            skipUnsafeBranch()
                        }
                    }
                },
                branchBlockName = "catch",
                branch = {
                    val exceptionPtr = exceptionBucket.buildPhi()
                    expression.throwableVariable.emitRead = { exceptionPtr }
                    expression.throwableVariable.emitWrite = {
                        throw CodeGenerationException("Cannot write to the exception variable of a catch")
                    }
                    val catchpadResult = emitExpressionCode(
                        expression.catchpad,
                        functionReturnType,
                        functionHasNothrowAbi,
                        expressionResultUsed,
                        tryContext,
                    )
                    when (catchpadResult) {
                        is ExpressionResult.Terminated -> catchpadResult.termination
                        is ExpressionResult.Value -> {
                            resultBucket?.setBranchResult(catchpadResult.value)
                            concludeBranch()
                        }
                    }
                }
            )

            return ExpressionResult.Value(
                resultBucket?.buildPhi() ?: context.poisonValue(tryCatchResultLlvmType)
            )
        }
        is IrImplicitEvaluationExpression -> {
            val result = emitCode(
                expression.code,
                functionReturnType,
                functionHasNothrowAbi,
                expressionResultUsed,
                tryContext,
            )
            return when (result) {
                is ExecutableResult.ExecutionOngoing,
                is ExpressionResult.Value -> ExpressionResult.Value(expression.implicitValue.declaration.llvmValue)
                is ExpressionResult.Terminated -> result
            }
        }
        is IrNotReallyAnExpression -> throw CodeGenerationException("Cannot emit expression evaluation code for an ${expression::class.simpleName}")
    }
}

internal fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.emitIsNull(
    value: IrTemporaryValueReference,
): LlvmValue<LlvmBooleanType> {
    if (!value.type.isNullable) {
        return context.i1(false)
    }

    return isNull(
        value.declaration.llvmValue
            .reinterpretAs(PointerToAnyEmergeValue)
    )
}

private class IfElseExprBranchEmitter<R : LlvmType>(
    val branchCode: IrImplicitEvaluationExpression,
    val valueStorage: PhiBucket<R>?,
    val valueStorageIrType: IrType,
    val functionHasNothrowAbi: Boolean,
    val functionReturnType: IrType,
    val tryContext: TryContext?,
) {
    lateinit var branchResult: ExecutableResult
        private set

    val generatorFn: BasicBlockBuilder.Branch<EmergeLlvmContext, LlvmType>.() -> BasicBlockBuilder.Termination = {
        val localBranchResult = emitExpressionCode(
            branchCode,
            this@IfElseExprBranchEmitter.functionReturnType,
            functionHasNothrowAbi,
            expressionResultUsed = valueStorage != null,
            tryContext,
        )
        branchResult = localBranchResult
        when (localBranchResult) {
            is ExpressionResult.Value -> {
                if (valueStorage != null) {
                    if (localBranchResult.value.type is LlvmVoidType) {
                        valueStorage.setBranchResult(context.poisonValue(valueStorage.type))
                    } else {
                        val boxedValue = autoBoxOrUnbox(localBranchResult.value, branchCode.evaluatesTo, valueStorageIrType)
                        valueStorage.setBranchResult(boxedValue as LlvmValue<R>)
                    }
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

private fun BasicBlockBuilder<EmergeLlvmContext, LlvmType>.getPointerToStructMember(
    structPointer: LlvmValue<*>,
    member: IrClass.Field
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

// todo: move to utils package
internal fun IrType.findSimpleTypeBound(): IrSimpleType {
    var carry: IrType = this
    while (carry !is IrSimpleType) {
        carry = when (carry) {
            is IrParameterizedType -> carry.simpleType
            is IrGenericTypeReference -> carry.effectiveBound
            else -> error("how the hell did this happen??")
        }
    }

    return carry
}

private sealed interface ArrayDispatchOverride {
    /** there is no override, the regular approach works */
    object None : ArrayDispatchOverride
    /** invoke this intrinsic instead */
    class InvokeIntrinsic(val intrinsic: KotlinLlvmFunction<EmergeLlvmContext, *>) : ArrayDispatchOverride
    /** invoke a virtual function dispatched on the array object */
    class InvokeVirtual(val hash: ULong, val fnType: LlvmFunctionType<*>) : ArrayDispatchOverride

    companion object {
        /**
         * on a method invocation on an array, this method determines whether the invocation is an access that can be
         * optimized; and if so, how
         */
        fun findFor(invocation: IrStaticDispatchFunctionInvocationExpression, context: EmergeLlvmContext): ArrayDispatchOverride {
            return if (invocation.function.declaresReceiver) {
                findForInstanceFunction(invocation, context)
            } else {
                findForStaticFunction(invocation, context)
            }
        }

        private fun findForInstanceFunction(invocation: IrStaticDispatchFunctionInvocationExpression, context: EmergeLlvmContext): ArrayDispatchOverride {
            val elementTypeArg = (invocation.arguments.first().type as IrParameterizedType).arguments.getValue("Element")

            val elementTypeBound = elementTypeArg.type.findSimpleTypeBound().baseType
            val accessType = if (elementTypeBound.canonicalName.toString() == "emerge.core.Any") {
                if (elementTypeArg.type !is IrGenericTypeReference && elementTypeArg.variance == IrTypeVariance.INVARIANT) {
                    ArrayAccessType.REFERENCE_TYPE_DIRECT
                } else {
                    ArrayAccessType.VIRTUAL
                }
            } else if (elementTypeBound.autoboxer is Autoboxer.PrimitiveType) {
                if (elementTypeArg.variance == IrTypeVariance.IN) {
                    ArrayAccessType.VIRTUAL
                } else {
                    ArrayAccessType.VALUE_TYPE_DIRECT
                }
            } else {
                ArrayAccessType.REFERENCE_TYPE_DIRECT
            }

            if (invocation.function.canonicalName.simpleName == GET_AT_INDEX_FN_NAME && invocation.function.parameters.size == 2) {
                when (accessType) {
                    ArrayAccessType.VIRTUAL -> return InvokeVirtual(
                        EmergeArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT_FALLIBLE,
                        context.registerIntrinsic(arrayAbstractFallibleGet).type,
                    )
                    ArrayAccessType.VALUE_TYPE_DIRECT -> return InvokeIntrinsic(when (elementTypeBound) {
                        context.rawS8Clazz -> EmergeS8ArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawU8Clazz -> EmergeU8ArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawS16Clazz -> EmergeS16ArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawU16Clazz -> EmergeU16ArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawS32Clazz -> EmergeS32ArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawU32Clazz -> EmergeU32ArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawS64Clazz -> EmergeS64ArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawU64Clazz -> EmergeU64ArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawSWordClazz -> EmergeSWordArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawUWordClazz -> EmergeUWordArrayType.rawGetterWithFallibleBoundsCheck
                        context.rawBoolClazz -> EmergeBooleanArrayType.rawGetterWithFallibleBoundsCheck
                        else -> throw CodeGenerationException("No value type direct access intrinsic available for ${elementTypeBound.canonicalName}")
                    })
                    ArrayAccessType.REFERENCE_TYPE_DIRECT -> return InvokeIntrinsic(
                        EmergeReferenceArrayType.rawGetterWithFallibleBoundsCheck
                    )
                }
            } else if (invocation.function.canonicalName.simpleName == SET_AT_INDEX_FN_NAME && invocation.function.parameters.size == 3) {
                when (accessType) {
                    ArrayAccessType.VIRTUAL -> return InvokeVirtual(
                        EmergeArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT_FALLIBLE,
                        context.registerIntrinsic(arrayAbstractFallibleSet).type,
                    )

                    ArrayAccessType.VALUE_TYPE_DIRECT -> return InvokeIntrinsic(
                        when (elementTypeBound) {
                            context.rawS8Clazz -> EmergeS8ArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawU8Clazz -> EmergeU8ArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawS16Clazz -> EmergeS16ArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawU16Clazz -> EmergeU16ArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawS32Clazz -> EmergeS32ArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawU32Clazz -> EmergeU32ArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawS64Clazz -> EmergeS64ArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawU64Clazz -> EmergeU64ArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawSWordClazz -> EmergeSWordArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawUWordClazz -> EmergeUWordArrayType.rawSetterWithFallibleBoundsCheck
                            context.rawBoolClazz -> EmergeBooleanArrayType.rawSetterWithFallibleBoundsCheck
                            else -> throw CodeGenerationException("No value type direct access intrinsic available for ${elementTypeBound.canonicalName}")
                        }
                    )

                    ArrayAccessType.REFERENCE_TYPE_DIRECT -> return InvokeIntrinsic(
                        EmergeReferenceArrayType.rawSetterWithFallibleBoundsCheck
                    )
                }
            } else if (invocation.function.canonicalName.simpleName == "getOrPanic" && invocation.function.parameters.size == 2) {
                when (accessType) {
                    ArrayAccessType.VIRTUAL -> return InvokeVirtual(
                        EmergeArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT_PANIC,
                        context.registerIntrinsic(arrayAbstractFallibleGet).type,
                    )

                    ArrayAccessType.VALUE_TYPE_DIRECT -> return InvokeIntrinsic(
                        when (elementTypeBound) {
                            context.rawS8Clazz -> EmergeS8ArrayType.rawGetterWithPanicBoundsCheck
                            context.rawU8Clazz -> EmergeU8ArrayType.rawGetterWithPanicBoundsCheck
                            context.rawS16Clazz -> EmergeS16ArrayType.rawGetterWithPanicBoundsCheck
                            context.rawU16Clazz -> EmergeU16ArrayType.rawGetterWithPanicBoundsCheck
                            context.rawS32Clazz -> EmergeS32ArrayType.rawGetterWithPanicBoundsCheck
                            context.rawU32Clazz -> EmergeU32ArrayType.rawGetterWithPanicBoundsCheck
                            context.rawS64Clazz -> EmergeS64ArrayType.rawGetterWithPanicBoundsCheck
                            context.rawU64Clazz -> EmergeU64ArrayType.rawGetterWithPanicBoundsCheck
                            context.rawSWordClazz -> EmergeSWordArrayType.rawGetterWithPanicBoundsCheck
                            context.rawUWordClazz -> EmergeUWordArrayType.rawGetterWithPanicBoundsCheck
                            context.rawBoolClazz -> EmergeBooleanArrayType.rawGetterWithPanicBoundsCheck
                            else -> throw CodeGenerationException("No value type direct access intrinsic available for ${elementTypeBound.canonicalName}")
                        }
                    )

                    ArrayAccessType.REFERENCE_TYPE_DIRECT -> return InvokeIntrinsic(
                        EmergeReferenceArrayType.rawGetterWithPanicBoundsCheck
                    )
                }
            } else if (invocation.function.canonicalName.simpleName == "setOrPanic" && invocation.function.parameters.size == 3) {
                when (accessType) {
                    ArrayAccessType.VIRTUAL -> return InvokeVirtual(
                        EmergeArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT_PANIC,
                        context.registerIntrinsic(arrayAbstractPanicSet).type,
                    )

                    ArrayAccessType.VALUE_TYPE_DIRECT -> return InvokeIntrinsic(
                        when (elementTypeBound) {
                            context.rawS8Clazz -> EmergeS8ArrayType.rawSetterWithPanicBoundsCheck
                            context.rawU8Clazz -> EmergeU8ArrayType.rawSetterWithPanicBoundsCheck
                            context.rawS16Clazz -> EmergeS16ArrayType.rawSetterWithPanicBoundsCheck
                            context.rawU16Clazz -> EmergeU16ArrayType.rawSetterWithPanicBoundsCheck
                            context.rawS32Clazz -> EmergeS32ArrayType.rawSetterWithPanicBoundsCheck
                            context.rawU32Clazz -> EmergeU32ArrayType.rawSetterWithPanicBoundsCheck
                            context.rawS64Clazz -> EmergeS64ArrayType.rawSetterWithPanicBoundsCheck
                            context.rawU64Clazz -> EmergeU64ArrayType.rawSetterWithPanicBoundsCheck
                            context.rawSWordClazz -> EmergeSWordArrayType.rawSetterWithPanicBoundsCheck
                            context.rawUWordClazz -> EmergeUWordArrayType.rawSetterWithPanicBoundsCheck
                            context.rawBoolClazz -> EmergeBooleanArrayType.rawSetterWithPanicBoundsCheck
                            else -> throw CodeGenerationException("No value type direct access intrinsic available for ${elementTypeBound.canonicalName}")
                        }
                    )

                    ArrayAccessType.REFERENCE_TYPE_DIRECT -> return InvokeIntrinsic(
                        EmergeReferenceArrayType.rawSetterWithPanicBoundsCheck
                    )
                }
            } else {
                return None
            }
        }

        private fun findForStaticFunction(invocation: IrStaticDispatchFunctionInvocationExpression, context: EmergeLlvmContext): ArrayDispatchOverride {
            if (invocation.function.canonicalName.simpleName == "new" && invocation.function.parameters.size == 2) {
                val elementTypeArg = (invocation.evaluatesTo as IrParameterizedType).arguments.getValue("Element")
                val elementTypeBound = elementTypeArg.type.findSimpleTypeBound().baseType
                return InvokeIntrinsic(when (elementTypeBound) {
                    context.rawS8Clazz -> EmergeS8ArrayType.defaultValueConstructor
                    context.rawU8Clazz -> EmergeU8ArrayType.defaultValueConstructor
                    context.rawS16Clazz -> EmergeS16ArrayType.defaultValueConstructor
                    context.rawU16Clazz -> EmergeU16ArrayType.defaultValueConstructor
                    context.rawS32Clazz -> EmergeS32ArrayType.defaultValueConstructor
                    context.rawU32Clazz -> EmergeU32ArrayType.defaultValueConstructor
                    context.rawS64Clazz -> EmergeS64ArrayType.defaultValueConstructor
                    context.rawU64Clazz -> EmergeU64ArrayType.defaultValueConstructor
                    context.rawSWordClazz -> EmergeSWordArrayType.defaultValueConstructor
                    context.rawUWordClazz -> EmergeUWordArrayType.defaultValueConstructor
                    context.rawBoolClazz -> EmergeBooleanArrayType.defaultValueConstructor
                    else -> EmergeReferenceArrayType.defaultValueConstructor
                })
            }

            if (invocation.function.canonicalName.simpleName == "copy" && invocation.function.parameters.size == 5) {
                val elementType = (invocation.typeArgumentsAtCallSite.getValue("T")).findSimpleTypeBound().baseType
                return when (elementType) {
                    context.rawS8Clazz,
                    context.rawU8Clazz -> InvokeIntrinsic(EmergeI8ArrayCopyFn)
                    context.rawS16Clazz,
                    context.rawU16Clazz -> InvokeIntrinsic(EmergeI16ArrayCopyFn)
                    context.rawS32Clazz,
                    context.rawU32Clazz -> InvokeIntrinsic(EmergeI32ArrayCopyFn)
                    context.rawS64Clazz,
                    context.rawU64Clazz -> InvokeIntrinsic(EmergeI64ArrayCopyFn)
                    context.rawSWordClazz,
                    context.rawUWordClazz -> InvokeIntrinsic(EmergeWordArrayCopyFn)
                    context.rawBoolClazz -> InvokeIntrinsic(EmergeBoolArrayCopyFn)
                    else -> None
                }
            }

            return None
        }
    }
}

private enum class ArrayAccessType {
    /** invoke the get and set functions through the vtable */
    VIRTUAL,
    /** optimized code for direct array access, depending on the value type */
    VALUE_TYPE_DIRECT,
    /** optimized code for direct array access, normed ptr-size because its references */
    REFERENCE_TYPE_DIRECT,
    ;
}