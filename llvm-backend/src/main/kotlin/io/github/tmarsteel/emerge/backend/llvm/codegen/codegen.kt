package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrAllocateObjectExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrBooleanLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrBreakStatement
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
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrIfExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrImplicitEvaluationExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrIntegerLiteralExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrInvocationExpression
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
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeVariance
import io.github.tmarsteel.emerge.backend.api.ir.IrUnregisterWeakReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrUpdateSourceLocationStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import io.github.tmarsteel.emerge.backend.api.ir.IrWhileLoop
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer.Companion.assureBoxed
import io.github.tmarsteel.emerge.backend.llvm.Autoboxer.Companion.requireNotAutoboxed
import io.github.tmarsteel.emerge.backend.llvm.StateTackDelegate
import io.github.tmarsteel.emerge.backend.llvm.autoboxer
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction.Companion.callIntrinsic
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.i1
import io.github.tmarsteel.emerge.backend.llvm.dsl.i16
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i64
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.emitBreak
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeBoolArrayCopyFn
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeBooleanArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
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
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.afterReferenceCreated
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.afterReferenceDropped
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arrayAbstractGet
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arrayAbstractSet
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.arraySize
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.getDynamicCallAddress
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.registerWeakReference
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.unregisterWeakReference
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word
import io.github.tmarsteel.emerge.backend.llvm.isUnit
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
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
    functionReturnType: IrType,
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
            val valueResult = emitExpressionCode(code.value, functionReturnType)
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
                        emitCode(component, functionReturnType)
                    } else {
                        accResult
                    }
                }

            if (resultAfterNonImplicitCode is ExpressionResult.Terminated) {
                return resultAfterNonImplicitCode
            }

            return code.components.lastOrNull()?.let { emitCode(it, functionReturnType) }
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
            val valueForAssignment: LlvmValue<*> = assureBoxed(code.value, code.target.type)

            when (val localTarget = code.target) {
                is IrAssignmentStatement.Target.Variable -> {
                    localTarget.declaration.emitWrite!!(this, valueForAssignment)
                }
                is IrAssignmentStatement.Target.ClassMemberVariable -> {
                    // TODO: autoboxing
                    val memberPointer = getPointerToStructMember(localTarget.objectValue.declaration.llvmValue, localTarget.memberVariable)
                    store(valueForAssignment, memberPointer)
                }
            }
            return ExecutableResult.ExecutionOngoing
        }
        is IrReturnStatement -> {
            // TODO: unit return to unit declaration

            val returnValue = assureBoxed(code.value, functionReturnType)
            return ExpressionResult.Terminated(ret(returnValue))
        }
        is IrWhileLoop -> {
            var conditionTermination: ExpressionResult.Terminated? = null
            loop(
                header = {
                    code.emitBreak = { breakLoop() }
                    val conditionResult = emitExpressionCode(code.condition, functionReturnType)
                    if (conditionResult is ExpressionResult.Terminated) {
                        conditionTermination = conditionResult
                        breakLoop()
                    } else {
                        conditionTermination = null
                    }
                    val conditionValue = (conditionResult as ExpressionResult.Value).value
                    check(conditionValue.type == LlvmBooleanType)
                    @Suppress("UNCHECKED_CAST")
                    conditionValue as LlvmValue<LlvmBooleanType>

                    conditionalBranch(
                        condition = conditionValue,
                        ifTrue = { doIteration() },
                    )
                    breakLoop()
                },
                body = {
                    code.emitBreak = { breakLoop() }
                    emitCode(code.body, functionReturnType)
                    loopContinue()
                }
            )

            StateTackDelegate.reset(code, IrWhileLoop::emitBreak)

            return conditionTermination ?: ExecutableResult.ExecutionOngoing
        }
        is IrBreakStatement -> {
            return ExpressionResult.Terminated(code.fromLoop.emitBreak!!())
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
    functionReturnType: IrType,
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
            if (expression.base.type.findSimpleTypeBound().baseType.canonicalName.toString() == "emerge.core.Array") {
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
                require(autoboxer !is Autoboxer.PrimitiveType) { "Cannot allocate a valuetype on the heap (encountered ${expression.clazz})"}
            }
            return ExpressionResult.Value(
                expression.clazz.llvmType.allocateUninitializedDynamicObject(this),
            )
        }
        is IrInvocationExpression -> when (expression) {
            is IrStaticDispatchFunctionInvocationExpression -> {
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
                            return ExpressionResult.Value(
                                call(
                                    addr,
                                    override.fnType,
                                    expression.arguments.zip(expression.function.parameters)
                                        .map { (argument, parameter) -> assureBoxed(argument, parameter.type) }
                                )
                            )
                        }

                        is ArrayDispatchOverride.InvokeIntrinsic -> {
                            // IMPORTANT! this deliberately doesn't box the arguments because that would box primitives
                            // in exactly a situation where that shouldn't happen.
                            return ExpressionResult.Value(
                                call(
                                    context.registerIntrinsic(override.intrinsic),
                                    expression.arguments.map { it.declaration.llvmValue })
                            )
                        }

                        else -> {}
                    }
                }

                // general handling
                val llvmFunction = expression.function.llvmRef
                    ?: throw CodeGenerationException("Missing implementation for ${expression.function.canonicalName}")
                val callInstruction = call(
                    llvmFunction,
                    expression.arguments.zip(expression.function.parameters)
                        .map { (argument, parameter) -> assureBoxed(argument, parameter.type) },
                )
                return ExpressionResult.Value(
                    if (expression.evaluatesTo.isUnit) {
                        context.pointerToPointerToUnitInstance
                    } else {
                        callInstruction
                    }
                )
            }

            is IrDynamicDispatchFunctionInvocationExpression -> {
                val argumentsForInvocation = expression.arguments.zip(expression.function.parameters)
                    .map { (argument, parameter) -> assureBoxed(argument, parameter.type) }

                val targetAddr = callIntrinsic(
                    getDynamicCallAddress, listOf(
                        expression.dispatchOn.declaration.llvmValue,
                        context.word(expression.function.signatureHashes.first()),
                    )
                )
                val callInstruction = call(targetAddr, expression.function.llvmFunctionType, argumentsForInvocation)
                return ExpressionResult.Value(
                    if (expression.evaluatesTo.isUnit) {
                        context.pointerToPointerToUnitInstance
                    } else {
                        callInstruction
                    }
                )
            }
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
                        val branchCodeResult = this@thenBranch.emitCode(expression.thenBranch.code, functionReturnType)
                        (branchCodeResult as? ExpressionResult.Terminated)?.termination ?: concludeBranch()
                    }
                )
                return ExpressionResult.Value(context.pointerToPointerToUnitInstance.dereference())
            }

            val valueHolder = alloca(context.getReferenceSiteType(expression.evaluatesTo))

            val thenEmitter = BranchEmitter(expression.thenBranch, valueHolder, functionReturnType)
            val elseEmitter = BranchEmitter(expression.elseBranch!!, valueHolder, functionReturnType)

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
        is IrImplicitEvaluationExpression -> {
            val result = emitCode(expression.code, functionReturnType)
            return when (result) {
                is ExecutableResult.ExecutionOngoing,
                is ExpressionResult.Value -> ExpressionResult.Value(expression.implicitValue.declaration.llvmValue)
                is ExpressionResult.Terminated -> result
            }
        }
        is IrNotReallyAnExpression -> throw CodeGenerationException("Cannot emit expression evaluation code for an ${expression::class.simpleName}")
    }
}

private class BranchEmitter(
    val branchCode: IrImplicitEvaluationExpression,
    val valueStorage: LlvmValue<LlvmPointerType<LlvmType>>?,
    val functionReturnType: IrType,
) {
    lateinit var branchResult: ExecutableResult
        private set

    val generatorFn: BasicBlockBuilder.Branch<EmergeLlvmContext, LlvmType>.() -> BasicBlockBuilder.Termination = {
        val localBranchResult = emitExpressionCode(branchCode, functionReturnType)
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

private fun IrType.findSimpleTypeBound(): IrSimpleType {
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

            if (invocation.function.canonicalName.simpleName == "get" && invocation.function.parameters.size == 2) {
                when (accessType) {
                    ArrayAccessType.VIRTUAL -> return InvokeVirtual(
                        EmergeArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT,
                        context.registerIntrinsic(arrayAbstractGet).type,
                    )
                    ArrayAccessType.VALUE_TYPE_DIRECT -> return InvokeIntrinsic(when (elementTypeBound) {
                        context.rawS8Clazz -> EmergeS8ArrayType.getRawGetter(false)
                        context.rawU8Clazz -> EmergeU8ArrayType.getRawGetter(false)
                        context.rawS16Clazz -> EmergeS16ArrayType.getRawGetter(false)
                        context.rawU16Clazz -> EmergeU16ArrayType.getRawGetter(false)
                        context.rawS32Clazz -> EmergeS32ArrayType.getRawGetter(false)
                        context.rawU32Clazz -> EmergeU32ArrayType.getRawGetter(false)
                        context.rawS64Clazz -> EmergeS64ArrayType.getRawGetter(false)
                        context.rawU64Clazz -> EmergeU64ArrayType.getRawGetter(false)
                        context.rawSWordClazz -> EmergeSWordArrayType.getRawGetter(false)
                        context.rawUWordClazz -> EmergeUWordArrayType.getRawGetter(false)
                        context.rawBoolClazz -> EmergeBooleanArrayType.getRawGetter(false)
                        else -> throw CodeGenerationException("No value type direct access intrinsic available for ${elementTypeBound.canonicalName}")
                    })
                    ArrayAccessType.REFERENCE_TYPE_DIRECT -> return InvokeIntrinsic(
                        EmergeReferenceArrayType.getRawGetter(false)
                    )
                }
            } else if (invocation.function.canonicalName.simpleName == "set" && invocation.function.parameters.size == 3) {
                when (accessType) {
                    ArrayAccessType.VIRTUAL -> return InvokeVirtual(
                        EmergeArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT,
                        context.registerIntrinsic(arrayAbstractSet).type,
                    )
                    ArrayAccessType.VALUE_TYPE_DIRECT -> return InvokeIntrinsic(when (elementTypeBound) {
                        context.rawS8Clazz -> EmergeS8ArrayType.getRawSetter(false)
                        context.rawU8Clazz -> EmergeU8ArrayType.getRawSetter(false)
                        context.rawS16Clazz -> EmergeS16ArrayType.getRawSetter(false)
                        context.rawU16Clazz -> EmergeU16ArrayType.getRawSetter(false)
                        context.rawS32Clazz -> EmergeS32ArrayType.getRawSetter(false)
                        context.rawU32Clazz -> EmergeU32ArrayType.getRawSetter(false)
                        context.rawS64Clazz -> EmergeS64ArrayType.getRawSetter(false)
                        context.rawU64Clazz -> EmergeU64ArrayType.getRawSetter(false)
                        context.rawSWordClazz -> EmergeSWordArrayType.getRawSetter(false)
                        context.rawUWordClazz -> EmergeUWordArrayType.getRawSetter(false)
                        context.rawBoolClazz -> EmergeBooleanArrayType.getRawSetter(false)
                        else -> throw CodeGenerationException("No value type direct access intrinsic available for ${elementTypeBound.canonicalName}")
                    })
                    ArrayAccessType.REFERENCE_TYPE_DIRECT -> return InvokeIntrinsic(
                        EmergeReferenceArrayType.getRawSetter(false)
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