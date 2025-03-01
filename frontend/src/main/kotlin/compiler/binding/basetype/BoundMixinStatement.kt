package compiler.binding.basetype

import compiler.InternalCompilerError
import compiler.ast.AstMixinStatement
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundStatement
import compiler.binding.ImpurityVisitor
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
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
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

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        expression.setNothrow(boundary)
    }

    private val expectedType: BoundTypeReference by lazy {
        context.swCtx.any.baseReference
            .withMutability(TypeMutability.EXCLUSIVE)
            .withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            expression.semanticAnalysisPhase1(diagnosis)
            expression.markEvaluationResultUsed()
            expression.setExpectedEvaluationResultType(expectedType, diagnosis)
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

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            expression.semanticAnalysisPhase2(diagnosis)
            expression.type?.evaluateAssignabilityTo(expectedType, expression.declaration.span)?.let(diagnosis::add)
            registration = context.registerMixin(this, expression.type ?: context.swCtx.any.baseReference, diagnosis)?.also {
                it.addDestructingAction(this::generateDestructorCode)
            }
            expression.markEvaluationResultCaptured(TypeMutability.EXCLUSIVE)
        }
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        expression.setExpectedReturnType(type, diagnosis)
    }

    var used = false
        private set
    fun assignToFunction(fnNeedingMixin: PossiblyMixedInBoundMemberFunction) {
        seanHelper.requirePhase2Done()
        fnNeedingMixin.assignMixin(registration!!)
        used = true
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            expression.semanticAnalysisPhase3(diagnosis)
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        expression.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        expression.visitWritesBeyond(boundary, visitor)
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