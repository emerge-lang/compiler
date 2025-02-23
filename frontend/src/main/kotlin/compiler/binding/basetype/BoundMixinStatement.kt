package compiler.binding.basetype

import compiler.InternalCompilerError
import compiler.ast.AstMixinStatement
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundExecutable
import compiler.binding.BoundStatement
import compiler.binding.IrAssignmentStatementImpl
import compiler.binding.IrAssignmentStatementTargetClassFieldImpl
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SeanHelper
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.IrClassFieldAccessExpressionImpl
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class BoundMixinStatement(
    val expression: BoundExpression<*>,
    override val declaration: AstMixinStatement,
) : BoundStatement<AstMixinStatement> {
    override val context = expression.context
    override val modifiedContext = MutableExecutionScopedCTContext.deriveFrom(expression.modifiedContext)

    override val throwBehavior: SideEffectPrediction? get()= expression.throwBehavior
    override val returnBehavior: SideEffectPrediction? get()= expression.returnBehavior

    private val seanHelper = SeanHelper()

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        expression.setNothrow(boundary)
    }

    private val expectedType: BoundTypeReference by lazy {
        context.swCtx.any.baseReference
            .withMutability(TypeMutability.EXCLUSIVE)
            .withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val reportings = expression.semanticAnalysisPhase1()
            expression.markEvaluationResultUsed()
            expression.setExpectedEvaluationResultType(expectedType)
            return@phase1 reportings
        }
    }

    /**
     * Initialized during [semanticAnalysisPhase2]
     */
    private var registration: ExecutionScopedCTContext.MixinRegistration? = null

    /**
     * the type of this mixin, initialized during [semanticAnalysisPhase2]
     */
    val type: BoundTypeReference? get() = expression.type

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            val reportings = expression.semanticAnalysisPhase2().toMutableSet()
            expression.type?.evaluateAssignabilityTo(expectedType, expression.declaration.span)?.let(reportings::add)
            registration = context.registerMixin(this, expression.type ?: context.swCtx.any.baseReference, Diagnosis.addingTo(reportings))?.also {
                it.addDestructingAction(this::generateDestructorCode)
            }
            expression.markEvaluationResultCaptured(TypeMutability.EXCLUSIVE)
            return@phase2 reportings
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference) {
        expression.setExpectedReturnType(type)
    }

    private var used = false
    fun assignToFunction(fnNeedingMixin: PossiblyMixedInBoundMemberFunction) {
        seanHelper.requirePhase2Done()
        fnNeedingMixin.assignMixin(registration!!)
        used = true
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            val reportings = expression.semanticAnalysisPhase3().toMutableSet()
            if (!used) {
                reportings.add(Reporting.unusedMixin(this))
            }
            return@phase3 reportings
        }
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return expression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<*>> {
        return expression.findWritesBeyond(boundary)
    }

    override fun toBackendIrStatement(): IrExecutable {
        val selfVariable = context.resolveVariable("self", true)
            ?: throw InternalCompilerError("Couldn't find a self value to generate IR for mixin at ${declaration.span}")
        val selfValueTemporary = IrCreateTemporaryValueImpl(IrVariableAccessExpressionImpl(selfVariable.backendIrDeclaration))
        val mixinValueTemporary = IrCreateTemporaryValueImpl(expression.toBackendIrExpression())

        return IrCodeChunkImpl(listOfNotNull(
            selfValueTemporary,
            mixinValueTemporary,
            IrCreateStrongReferenceStatementImpl(mixinValueTemporary).takeUnless { expression.isEvaluationResultReferenceCounted },
            IrAssignmentStatementImpl(
                IrAssignmentStatementTargetClassFieldImpl(
                    registration!!.obtainField().toBackendIr(),
                    IrTemporaryValueReferenceImpl(selfValueTemporary),
                ),
                IrTemporaryValueReferenceImpl(mixinValueTemporary),
            ),
        ))

        // the destructuring code is added in sean2
    }

    private fun generateDestructorCode(self: IrCreateTemporaryValue): IrExecutable {
        val mixinValue = IrCreateTemporaryValueImpl(IrClassFieldAccessExpressionImpl(
            IrTemporaryValueReferenceImpl(self),
            registration!!.obtainField().toBackendIr(),
            expression.type!!.toBackendIr(),
        ))
        return IrCodeChunkImpl(listOf(
            mixinValue,
            IrDropStrongReferenceStatementImpl(mixinValue),
        ))
    }
}