package compiler.binding.expression

import compiler.ast.expression.AstTopLevelFunctionReference
import compiler.binding.BoundFunction
import compiler.binding.SeanHelper
import compiler.binding.SideEffectPrediction
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundFunctionType
import compiler.binding.type.BoundTypeReference
import compiler.handleCyclicInvocation
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrTopLevelFunctionReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundTopLevelFunctionReference(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstTopLevelFunctionReference,
) : BoundExpression<AstTopLevelFunctionReference> {
    override var type: BoundFunctionType? = null
        private set

    override val throwBehavior: SideEffectPrediction = SideEffectPrediction.NEVER
    override val returnBehavior: SideEffectPrediction = SideEffectPrediction.NEVER

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        // nothing to do; this is effectively a literal/constant
    }

    private val seanHelper = SeanHelper()

    private lateinit var referredFunction: BoundFunction

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val overloads = context.getToplevelFunctionOverloadSetsBySimpleName(declaration.nameToken.value)
                .asSequence()
                .flatMap { it.overloads }
                .toList()

            if (overloads.isEmpty()) {
                return@phase1 listOf(Reporting.referencingUnknownFunction(this))
            }

            if (overloads.size > 1) {
                return@phase1 listOf(Reporting.ambiguousFunctionReference(this, overloads))
            }

            val localReferredFn = overloads.single()
            this.referredFunction = localReferredFn

            return@phase1 emptySet()
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2(runIfErrorsPreviously = false) {
            val reportings = mutableListOf<Reporting>()

            if (this.referredFunction.returnType == null) {
                reportings.addAll(handleCyclicInvocation(
                    context = this,
                    action = {
                        this.referredFunction.semanticAnalysisPhase2()
                        emptySet()
                    },
                    onCycle = {
                        setOf(Reporting.typeDeductionError("Cannot infer the type of this function reference because the type inference is cyclic here. Specify a return type explicitly.", declaration.span))
                    }
                ))
            }

            this.type = BoundFunctionType.fromReference(this, this.referredFunction)

            return@phase2 reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 { emptySet()  }
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // not used, referencing overloaded/ambiguous functions is not supported currently
    }

    override val isEvaluationResultReferenceCounted: Boolean = true
    override val isCompileTimeConstant: Boolean = true

    private val backendIr by lazy { IrTopLevelFunctionReferenceImpl(referredFunction, type!!) }
    override fun toBackendIrExpression(): IrExpression {
        return backendIr
    }
}

private class IrTopLevelFunctionReferenceImpl(
    val referredBoundFunction: BoundFunction,
    val boundType: BoundFunctionType,
) : IrTopLevelFunctionReference {
    override val referredFunction: IrFunction get() = referredBoundFunction.toBackendIr()
    override val evaluatesTo: IrType get()= boundType.toBackendIr()
}