package compiler.binding

import compiler.ast.AssignmentStatement
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.context.effect.VariableLifetime
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.lexer.IdentifierToken
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
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

    override fun additionalSemanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        targetVariable = context.resolveVariable(variableName.value)
        if (targetVariable == null) {
            reportings.add(Reporting.undefinedIdentifier(variableName))
        }

        return reportings
    }

    override fun assignmentTargetSemanticAnalysisPhase2(): Collection<Reporting> {
        return emptySet()
    }

    override val assignmentTargetType get() = targetVariable?.typeAtDeclarationTime

    override fun additionalSemanticAnalysisPhase2(): Collection<Reporting> {
        targetVariable?.also {
            _modifiedContext.trackSideEffect(VariableLifetime.Effect.NewValueAssigned(it))
        }
        return emptySet()
    }

    override fun setTargetNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        // variable write cannot throw
    }

    private lateinit var initializationStateBefore: VariableInitialization.State
    override fun additionalSemanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

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
                    reportings.add(Reporting.illegalAssignment("Variable ${targetVariable.name} may have already been initialized, cannot assign a value again", this))
                }
            }
            if (initializationStateBefore == VariableInitialization.State.INITIALIZED) {
                if (!targetVariable.isReAssignable) {
                    reportings.add(Reporting.illegalAssignment("Variable ${targetVariable.name} is already initialized, cannot re-assign", this))
                }
            }

            nothrowBoundary?.let { nothrowBoundary ->
                if (!thisAssignmentIsFirstInitialization) {
                    if (targetVariable.typeAtDeclarationTime?.destructorThrowBehavior != SideEffectPrediction.NEVER) {
                        reportings.add(Reporting.droppingReferenceToObjectWithThrowingConstructor(this, nothrowBoundary))
                    }
                }
            }
        }

        return reportings
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        if (targetVariable == null || context.containsWithinBoundary(targetVariable!!, boundary)) {
            return super.findWritesBeyond(boundary)
        }

        return super.findWritesBeyond(boundary) + listOf(this)
    }

    override fun toBackendIrStatement(): IrExecutable {
        val dropPreviousCode: List<IrExecutable> = when (initializationStateBefore) {
            VariableInitialization.State.NOT_INITIALIZED -> emptyList()
            else -> {
                var previousType = targetVariable!!.getTypeInContext(context)!!.toBackendIr()
                if (initializationStateBefore == VariableInitialization.State.MAYBE_INITIALIZED) {
                    // forces a null-check on the reference drop, preventing a null-pointer dereference when a maybe-initialized
                    // variable of a non-null type is being assigned to
                    previousType = previousType.asNullable()
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

        return IrCodeChunkImpl(dropPreviousCode + listOf(
            toAssignTemporary,
            assignStatement
        ))
    }
}

internal class IrAssignmentStatementTargetVariableImpl(
    override val declaration: IrVariableDeclaration,
): IrAssignmentStatement.Target.Variable