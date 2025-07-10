package compiler.binding

import compiler.ast.Executable
import compiler.ast.FunctionDeclaration
import compiler.ast.VariableOwnership
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.expression.ReturnValueFromFunctionUsage
import compiler.binding.impurity.DiagnosingImpurityVisitor
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.misc_ir.IrUpdateSourceLocationStatementImpl
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.typeDeductionError
import compiler.diagnostic.uncertainTermination
import compiler.diagnostic.varianceOnFunctionTypeParameter
import compiler.handleCyclicInvocation
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement

/**
 * Describes the presence/avaiability of a (class member) function in a context.
 * Refers to the original declaration and holds a reference to the appropriate context
 * so that [BaseType]s for receiver, parameters and return type can be resolved.
 */
abstract class BoundDeclaredFunction(
    final override val parentContext: CTContext,
    final override val functionRootContext: MutableExecutionScopedCTContext,
    val declaration: FunctionDeclaration,
    final override val attributes: BoundFunctionAttributeList,
    final override val declaredTypeParameters: List<BoundTypeParameter>,
    final override val parameters: BoundParameterList,
    val body: Body?,
) : BoundFunction {
    final override val declaredAt = declaration.declaredAt
    final override val name: String = declaration.name.value

    final override val allTypeParameters get()= functionRootContext.allTypeParameters.toList()

    final override val receiverType: BoundTypeReference?
        get() = parameters.declaredReceiver?.typeAtDeclarationTime

    final override val declaresReceiver = parameters.declaredReceiver != null

    final override var returnType: BoundTypeReference? = null
        private set

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            attributes.semanticAnalysisPhase1(diagnosis)

            declaredTypeParameters.forEach { it.semanticAnalysisPhase1(diagnosis) }
            parameters.semanticAnalysisPhase1(diagnosis)

            if (declaration.parsedReturnType != null) {
                returnType = functionRootContext.resolveType(declaration.parsedReturnType)
                if (body !is Body.SingleExpression) {
                    returnType = returnType?.defaultMutabilityTo(TypeMutability.READONLY)
                }
            }

            this.body?.semanticAnalysisPhase1(diagnosis)

            returnType?.let {
                body?.setExpectedReturnType(it, diagnosis)
            }
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            handleCyclicInvocation(
                context = this,
                action = { this.body?.semanticAnalysisPhase2(diagnosis) },
                onCycle = {
                    diagnosis.typeDeductionError(
                        "Cannot infer the return type of function $name because the type inference is cyclic here. Specify the type of one element explicitly.",
                        declaredAt
                    )
                }
            )

            if (returnType == null) {
                if (this.body is Body.SingleExpression) {
                    this.returnType = this.body.expression.type
                } else {
                    this.returnType = functionRootContext.swCtx.unit.baseReference
                        .withMutability(TypeMutability.READONLY)
                }
            }

            receiverType?.let {
                it.validate(TypeUseSite.InUsage(it.span, this), diagnosis)
            }
            parameterTypes.forEach {
                it?.validate(TypeUseSite.InUsage(it.span, this), diagnosis)
            }
            returnType?.let {
                val returnTypeUseSite = TypeUseSite.OutUsage(
                    declaration.parsedReturnType?.span
                        ?: this.declaredAt,
                    this,
                )
                it.validate(returnTypeUseSite, diagnosis)
            }
            declaredTypeParameters.forEach {
                it.semanticAnalysisPhase2(diagnosis)
                if (it.variance != TypeVariance.UNSPECIFIED) {
                    diagnosis.varianceOnFunctionTypeParameter(it)
                }
            }
            body?.semanticAnalysisPhase2(diagnosis)
            if (attributes.isDeclaredNothrow) {
                body?.setNothrow(NothrowViolationDiagnostic.SideEffectBoundary.Function(this))
            }

            attributes.firstAccessorAttribute?.kind?.validateContract(this, diagnosis)
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            declaredTypeParameters.forEach { it.semanticAnalysisPhase3(diagnosis) }

            if (body != null) {
                body.semanticAnalysisPhase3(diagnosis)

                if (BoundFunction.Purity.READONLY.contains(this.purity)) {
                    val diagnosingVisitor = DiagnosingImpurityVisitor(diagnosis, PurityViolationDiagnostic.SideEffectBoundary.Function(this))
                    handleCyclicInvocation(
                        context = this,
                        action = { body.visitWritesBeyond(functionRootContext, diagnosingVisitor) },
                        onCycle = {},
                    )

                    if (BoundFunction.Purity.PURE.contains(this.purity)) {
                        handleCyclicInvocation(
                            context = this,
                            action = { body.visitReadsBeyond(functionRootContext, diagnosingVisitor) },
                            onCycle = {},
                        )
                    }
                }

                // assure all paths return or throw
                val isGuaranteedToTerminate = body.returnBehavior == SideEffectPrediction.GUARANTEED || body.throwBehavior == SideEffectPrediction.GUARANTEED

                if (!isGuaranteedToTerminate) {
                    val localReturnType = returnType
                    // if the function is declared to return Unit a return of Unit is implied and should be inserted by backends
                    // if this is a single-expression function (fun a() = 3), return is implied
                    if (localReturnType == null || this.body !is Body.SingleExpression) {
                        val isImplicitUnitReturn = localReturnType is RootResolvedTypeReference && localReturnType.baseType == functionRootContext.swCtx.unit
                        if (!isImplicitUnitReturn) {
                            diagnosis.uncertainTermination(this)
                        }
                    }
                }
            }
        }
    }

    override fun validateAccessFrom(location: Span, diagnosis: Diagnosis) {
        return attributes.visibility.validateAccessFrom(location, this, diagnosis)
    }

    // refcounting for parameters
    init {
        if (body != null) {
            parameters.parameters.asSequence()
                .filter { it.ownershipAtDeclarationTime == VariableOwnership.CAPTURED }
                .forEach { param ->
                    functionRootContext.addDeferredCode(DeferredLocalVariableGCRelease(param))
                }
        }
    }

    fun getFullBodyBackendIr(): IrCodeChunk? {
        if (body == null) {
            return null
        }

        val refcountIncrements = ArrayList<IrExecutable>(parameters.parameters.size + 1)
        refcountIncrements.add(IrUpdateSourceLocationStatementImpl(declaredAt))
        parameters.parameters.asSequence()
            .filter { it.ownershipAtDeclarationTime == VariableOwnership.CAPTURED }
            .forEach { param ->
                val tmp = IrCreateTemporaryValueImpl(IrVariableAccessExpressionImpl(param.backendIrDeclaration))
                refcountIncrements.add(tmp)
                refcountIncrements.add(IrCreateStrongReferenceStatementImpl(tmp))
            }

        return IrCodeChunkImpl(refcountIncrements + body.toBackendIr().components)
    }

    sealed interface Body : BoundExecutable<Executable> {
        fun toBackendIr(): IrCodeChunk

        class SingleExpression(
            private val bodyDeclaration: FunctionDeclaration.Body.SingleExpression,
            val expression: BoundExpression<*>,
        ) : Body, BoundExecutable<Executable> by expression {
            override val returnBehavior = SideEffectPrediction.GUARANTEED

            private var expectedReturnType: BoundTypeReference? = null
            private val seanHelper = SeanHelper()

            override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
                expectedReturnType = type
                expression.setExpectedEvaluationResultType(type, diagnosis)
            }

            override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
                seanHelper.phase1(diagnosis) {
                    expression.semanticAnalysisPhase1(diagnosis)
                    expression.markEvaluationResultUsed()
                }
            }

            override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
                seanHelper.phase2(diagnosis) {
                    expression.semanticAnalysisPhase2(diagnosis)
                    expression.setEvaluationResultUsage(ReturnValueFromFunctionUsage(
                        expectedReturnType,
                        bodyDeclaration.equalsOperatorToken.span,
                    ))
                }
            }

            override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
                seanHelper.phase3(diagnosis) {
                    expression.semanticAnalysisPhase3(diagnosis)
                    expectedReturnType?.let { declaredReturnType ->
                        expression.type?.let { actualReturnType ->
                            actualReturnType.evaluateAssignabilityTo(declaredReturnType, expression.declaration.span)
                                ?.let(::ReturnTypeMismatchDiagnostic)
                                ?.let(diagnosis::add)
                        }
                    }
                }
            }

            override fun toBackendIr(): IrCodeChunk {
                val resultTemporary = IrCreateTemporaryValueImpl(expression.toBackendIrExpression())
                return IrCodeChunkImpl(listOf(
                    IrUpdateSourceLocationStatementImpl(expression.declaration.span),
                    resultTemporary,
                    object : IrReturnStatement {
                        override val value = IrTemporaryValueReferenceImpl(resultTemporary)
                    },
                ))
            }
        }

        class Full(val code: BoundCodeChunk) : Body, BoundExecutable<Executable> by code {
            override fun toBackendIr(): IrCodeChunk {
                return code.toBackendIrStatement()
            }
        }
    }
}