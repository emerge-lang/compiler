package compiler.binding

import compiler.*
import compiler.ast.Executable
import compiler.ast.FunctionDeclaration
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.misc_ir.IrUpdateSourceLocationStatementImpl
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.lexer.Span
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import compiler.reportings.ReturnTypeMismatchReporting
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement

/**
 * Describes the presence/avaiability of a (class member) function in a context.
 * Refers to the original declaration and holds a reference to the appropriate context
 * so that [BaseType]s for receiver, parameters and return type can be resolved.
 */
abstract class BoundDeclaredFunction(
    final override val context: CTContext,
    val declaration: FunctionDeclaration,
    final override val attributes: BoundFunctionAttributeList,
    final override val declaredTypeParameters: List<BoundTypeParameter>,
    final override val parameters: BoundParameterList,
    val body: Body?,
) : BoundFunction {
    final override val declaredAt = declaration.declaredAt
    final override val name: String = declaration.name.value

    final override val allTypeParameters get()= context.allTypeParameters.toList()

    final override val receiverType: BoundTypeReference?
        get() = parameters.declaredReceiver?.typeAtDeclarationTime

    final override val declaresReceiver = parameters.declaredReceiver != null

    final override var returnType: BoundTypeReference? = null
        private set

    final override val throwBehavior: SideEffectPrediction? get() {
        if (attributes.isDeclaredNothrow) {
            return SideEffectPrediction.NEVER
        }

        return handleCyclicInvocation(
            context = this,
            action = { body?.throwBehavior },
            onCycle = { SideEffectPrediction.POSSIBLY },
        )
    }

    private val seanHelper = SeanHelper()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val reportings = mutableSetOf<Reporting>()

            reportings.addAll(attributes.semanticAnalysisPhase1())

            declaredTypeParameters.map(BoundTypeParameter::semanticAnalysisPhase1).forEach(reportings::addAll)
            reportings.addAll(parameters.semanticAnalysisPhase1())

            if (declaration.parsedReturnType != null) {
                returnType = context.resolveType(declaration.parsedReturnType)
                if (body !is Body.SingleExpression) {
                    returnType = returnType?.defaultMutabilityTo(TypeMutability.IMMUTABLE)
                }
            }

            this.body?.semanticAnalysisPhase1()?.let(reportings::addAll)

            returnType?.let {
                body?.setExpectedReturnType(it)
            }

            return@phase1 reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            val reportings = mutableSetOf<Reporting>()

            handleCyclicInvocation(
                context = this,
                action = { this.body?.semanticAnalysisPhase2()?.let(reportings::addAll) },
                onCycle = {
                    Reporting.typeDeductionError(
                        "Cannot infer the return type of function $name because the type inference is cyclic here. Specify the type of one element explicitly.",
                        declaredAt
                    )
                }
            )

            if (returnType == null) {
                if (this.body is Body.SingleExpression) {
                    this.returnType = this.body.expression.type
                } else {
                    this.returnType = context.swCtx.unit.baseReference
                        .withMutability(TypeMutability.READONLY)
                }
            }

            receiverType?.let {
                it.validate(TypeUseSite.InUsage(it.span, this)).let(reportings::addAll)
            }
            parameterTypes.forEach {
                it?.validate(TypeUseSite.InUsage(it.span, this))?.let(reportings::addAll)
            }
            returnType?.let {
                val returnTypeUseSite = TypeUseSite.OutUsage(
                    declaration.parsedReturnType?.declaringNameToken?.span
                        ?: this.declaredAt,
                    this,
                )
                reportings.addAll(it.validate(returnTypeUseSite))
            }
            declaredTypeParameters.forEach {
                reportings.addAll(it.semanticAnalysisPhase2())
                if (it.variance != TypeVariance.UNSPECIFIED) {
                    reportings.add(Reporting.varianceOnFunctionTypeParameter(it))
                }
            }
            body?.semanticAnalysisPhase2()?.let(reportings::addAll)
            if (attributes.isDeclaredNothrow) {
                body?.setNothrow(NothrowViolationReporting.SideEffectBoundary.Function(this))
            }

            return@phase2 reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            val reportings = mutableSetOf<Reporting>()

            declaredTypeParameters.map(BoundTypeParameter::semanticAnalysisPhase3).forEach(reportings::addAll)

            if (body != null) {
                reportings += body.semanticAnalysisPhase3()

                if (BoundFunction.Purity.READONLY.contains(this.purity)) {
                    val statementsWritingBeyondFunctionContext = handleCyclicInvocation(
                        context = this,
                        action = { body.findWritesBeyond(context) },
                        onCycle = ::emptySet,
                    )

                    if (BoundFunction.Purity.PURE.contains(this.purity)) {
                        val statementsReadingBeyondFunctionContext = handleCyclicInvocation(
                            context = this,
                            action = { body.findReadsBeyond(context) },
                            onCycle = ::emptySet,
                        )
                        reportings.addAll(Reporting.purityViolations(statementsReadingBeyondFunctionContext, statementsWritingBeyondFunctionContext, this))
                    } else {
                        reportings.addAll(Reporting.readonlyViolations(statementsWritingBeyondFunctionContext, this))
                    }
                }

                // assure all paths return or throw
                val isGuaranteedToTerminate = body.returnBehavior == SideEffectPrediction.GUARANTEED || body.throwBehavior == SideEffectPrediction.GUARANTEED

                if (!isGuaranteedToTerminate) {
                    val localReturnType = returnType
                    // if the function is declared to return Unit a return of Unit is implied and should be inserted by backends
                    // if this is a single-expression function (fun a() = 3), return is implied
                    if (localReturnType == null || this.body !is Body.SingleExpression) {
                        val isImplicitUnitReturn = localReturnType is RootResolvedTypeReference && localReturnType.baseType == context.swCtx.unit
                        if (!isImplicitUnitReturn) {
                            reportings.add(Reporting.uncertainTermination(this))
                        }
                    }
                }
            }

            return@phase3 reportings
        }
    }

    override fun validateAccessFrom(location: Span): Collection<Reporting> {
        return attributes.visibility.validateAccessFrom(location, this)
    }

    sealed interface Body : BoundExecutable<Executable> {
        fun toBackendIr(): IrCodeChunk

        class SingleExpression(val expression: BoundExpression<*>) : Body, BoundExecutable<Executable> by expression {
            override val returnBehavior = SideEffectPrediction.GUARANTEED

            private var expectedReturnType: BoundTypeReference? = null

            override fun setExpectedReturnType(type: BoundTypeReference) {
                expectedReturnType = type
                expression.setExpectedEvaluationResultType(type)
            }

            override fun semanticAnalysisPhase1(): Collection<Reporting> {
                val reportings = expression.semanticAnalysisPhase1()
                expression.markEvaluationResultUsed()
                return reportings
            }

            override fun semanticAnalysisPhase3(): Collection<Reporting> {
                val reportings = mutableListOf<Reporting>()
                reportings.addAll(expression.semanticAnalysisPhase3())
                expectedReturnType?.let { declaredReturnType ->
                    expression.type?.let { actualReturnType ->
                        actualReturnType.evaluateAssignabilityTo(declaredReturnType, expression.declaration.span)
                            ?.let(::ReturnTypeMismatchReporting)
                            ?.let(reportings::add)
                    }
                }

                return reportings
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
                return code.toBackendIrStatement() // TODO: implicit unit return
            }
        }
    }
}