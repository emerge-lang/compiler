package compiler.binding

import compiler.ast.AssignmentStatement
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.context.effect.VariableLifetime
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.lexer.IdentifierToken
import compiler.reportings.Diagnosis
import compiler.reportings.Diagnostic
import compiler.reportings.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

class BoundVariableAssignmentStatement(
    context: ExecutionScopedCTContext,
    declaration: AssignmentStatement,
    val variableName: IdentifierToken,
    toAssignExpression: BoundExpression<*>,
) : BoundAssignmentStatement(context, declaration, toAssignExpression) {
    override val targetThrowBehavior = SideEffectPrediction.NEVER
    override val targetReturnBehavior = SideEffectPrediction.NEVER

    private var targetVariable: BoundVariable? = null

    override fun additionalSemanticAnalysisPhase1(diagnosis: Diagnosis) {
        targetVariable = context.resolveVariable(variableName.value)
        if (targetVariable == null) {
            diagnosis.add(Diagnostic.undefinedIdentifier(variableName))
        }
    }

    override fun assignmentTargetSemanticAnalysisPhase2(diagnosis: Diagnosis) {

    }

    override val assignmentTargetType get() = targetVariable?.typeAtDeclarationTime

    override fun additionalSemanticAnalysisPhase2(diagnosis: Diagnosis) {
        targetVariable?.also {
            _modifiedContext.trackSideEffect(VariableLifetime.Effect.NewValueAssigned(it))
        }
    }

    override fun setTargetNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        // variable write cannot throw
    }

    private lateinit var initializationStateBefore: VariableInitialization.State
    override fun additionalSemanticAnalysisPhase3(diagnosis: Diagnosis) {
        targetVariable?.let { targetVariable ->
            val repetitionRelativeToVariable = context.getRepetitionBehaviorRelativeTo(targetVariable.modifiedContext)

            initializationStateBefore = targetVariable.getInitializationStateInContext(context)
            val thisAssignmentIsFirstInitialization: Boolean = initializationStateBefore == VariableInitialization.State.NOT_INITIALIZED
            if (initializationStateBefore == VariableInitialization.State.NOT_INITIALIZED || initializationStateBefore == VariableInitialization.State.MAYBE_INITIALIZED) {
                _modifiedContext.trackSideEffect(VariableInitialization.WriteToVariableEffect(targetVariable))
            }
            if (initializationStateBefore == VariableInitialization.State.MAYBE_INITIALIZED || repetitionRelativeToVariable.mayRepeat) {
                if (targetVariable.isReAssignable) {
                    _modifiedContext.trackSideEffect(VariableInitialization.WriteToVariableEffect(targetVariable))
                } else {
                    diagnosis.add(Diagnostic.illegalAssignment("Variable ${targetVariable.name} may have already been initialized, cannot assign a value again", this))
                }
            }
            if (initializationStateBefore == VariableInitialization.State.INITIALIZED) {
                if (!targetVariable.isReAssignable) {
                    diagnosis.add(Diagnostic.illegalAssignment("Variable ${targetVariable.name} is already initialized, cannot re-assign", this))
                }
            }
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        toAssignExpression.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        targetVariable
            ?.takeIf { !context.containsWithinBoundary(it, boundary) }
            ?.let {
                visitor.visitWriteBeyondBoundary(boundary, this)
            }

        super.visitWritesBeyond(boundary, visitor)
    }


    override fun toBackendIrStatement(): IrExecutable {
        val dropPreviousCode: List<IrExecutable> = when (initializationStateBefore) {
            VariableInitialization.State.NOT_INITIALIZED -> emptyList()
            else -> {
                var previousType = targetVariable!!.getTypeInContext(context)!!.toBackendIr()
                if (initializationStateBefore == VariableInitialization.State.MAYBE_INITIALIZED) {
                    // forces a null-check on the reference drop, preventing a null-pointer dereference when a maybe-initialized
                    // variable of a non-null type is being assigned to
                    previousType = previousType.nullable()
                }
                val previousTemporary = IrCreateTemporaryValueImpl(
                    IrVariableAccessExpressionImpl(targetVariable!!.backendIrDeclaration),
                    previousType,
                )
                listOf(previousTemporary, IrDropStrongReferenceStatementImpl(previousTemporary))
            }
        }

        val toAssignTemporary = IrCreateTemporaryValueImpl(toAssignExpression.toBackendIrExpression())
        val assignStatement = IrAssignmentStatementImpl(
            IrAssignmentStatementTargetVariableImpl(targetVariable!!.backendIrDeclaration),
            IrTemporaryValueReferenceImpl(toAssignTemporary),
        )

        return IrCodeChunkImpl(listOfNotNull(
            toAssignTemporary,
            IrCreateStrongReferenceStatementImpl(toAssignTemporary).takeUnless { toAssignExpression.isEvaluationResultReferenceCounted },
        ) + dropPreviousCode + assignStatement)
    }
}

internal class IrAssignmentStatementTargetVariableImpl(
    override val declaration: IrVariableDeclaration,
): IrAssignmentStatement.Target.Variable