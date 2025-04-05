package compiler.binding

import compiler.ast.AssignmentStatement
import compiler.binding.SideEffectPrediction.Companion.combineSequentialExecution
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.ValueUsage
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.IrGenericTypeReferenceImpl
import compiler.binding.type.IrParameterizedTypeImpl
import compiler.binding.type.IrSimpleTypeImpl
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

abstract class BoundAssignmentStatement(
    override val context: ExecutionScopedCTContext,
    override val declaration: AssignmentStatement,
    val toAssignExpression: BoundExpression<*>
) : BoundStatement<AssignmentStatement> {
    protected abstract val targetThrowBehavior: SideEffectPrediction?
    protected abstract val targetReturnBehavior: SideEffectPrediction?

    final override val throwBehavior get() = targetThrowBehavior.combineSequentialExecution(toAssignExpression.throwBehavior)
    final override val returnBehavior get() = targetReturnBehavior.combineSequentialExecution(toAssignExpression.returnBehavior)

    protected val _modifiedContext = MutableExecutionScopedCTContext.deriveFrom(toAssignExpression.modifiedContext)
    override val modifiedContext: ExecutionScopedCTContext = _modifiedContext

    private val seanHelper = SeanHelper()

    final override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            toAssignExpression.semanticAnalysisPhase1(diagnosis)
            additionalSemanticAnalysisPhase1(diagnosis)
        }
    }

    protected abstract fun additionalSemanticAnalysisPhase1(diagnosis: Diagnosis)

    /**
     * does [SemanticallyAnalyzable.semanticAnalysisPhase2] only on the target of the assignment
     * with the goal of making [assignmentTargetType] available.
     */
    protected abstract fun assignmentTargetSemanticAnalysisPhase2(diagnosis: Diagnosis)

    /**
     * the type of the assignment target; if available, must be set after [assignmentTargetSemanticAnalysisPhase2]
     */
    protected abstract val assignmentTargetType: BoundTypeReference?
    protected abstract val assignedValueUsage: ValueUsage

    abstract fun additionalSemanticAnalysisPhase2(diagnosis: Diagnosis)

    final override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            toAssignExpression.markEvaluationResultUsed()

            assignmentTargetSemanticAnalysisPhase2(diagnosis)
            assignmentTargetType?.let { targetType ->
                toAssignExpression.setExpectedEvaluationResultType(targetType, diagnosis)
            }

            toAssignExpression.semanticAnalysisPhase2(diagnosis)
            additionalSemanticAnalysisPhase2(diagnosis)
            toAssignExpression.setEvaluationResultUsage(assignedValueUsage)

            toAssignExpression.type?.also { assignedType ->
                assignmentTargetType?.also { targetType ->
                    assignedType.evaluateAssignabilityTo(targetType, toAssignExpression.declaration.span)
                        ?.let(diagnosis::add)
                }
            }
        }
    }

    protected abstract fun setTargetNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary)

    protected var nothrowBoundary: NothrowViolationDiagnostic.SideEffectBoundary? = null
        private set
    final override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        seanHelper.requirePhase3NotDone()
        require(nothrowBoundary == null) { "setNothrow called more than once" }

        this.nothrowBoundary = boundary
        toAssignExpression.setNothrow(boundary)
        setTargetNothrow(boundary)
    }

    final override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            toAssignExpression.semanticAnalysisPhase3(diagnosis)
            additionalSemanticAnalysisPhase3(diagnosis)
        }
    }

    protected abstract fun additionalSemanticAnalysisPhase3(diagnosis: Diagnosis)

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        toAssignExpression.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        toAssignExpression.visitWritesBeyond(boundary, visitor)
    }

    protected fun IrType.nullable(): IrType = if (isNullable) this else when (this) {
        is IrSimpleType -> IrSimpleTypeImpl(this.baseType, mutability,true)
        is IrGenericTypeReference -> IrGenericTypeReferenceImpl(this.parameter, effectiveBound.nullable())
        is IrParameterizedType -> IrParameterizedTypeImpl(this.simpleType.nullable() as IrSimpleType, arguments)
    }
}

/**
 * [BoundAssignmentStatement] is a [BoundExpression] because the compiler wants to detect accidental use of `=` instead
 * of `==`. So [BoundAssignmentStatement.toBackendIrStatement] must return an [IrExpression], as per the [BoundExpression]
 * contract. Consequently, this class must also implement [IrExpression] even though it's not. Unavoidable.
 */
internal class IrAssignmentStatementImpl(
    override val target: IrAssignmentStatement.Target,
    override val value: IrTemporaryValueReference,
) : IrAssignmentStatement