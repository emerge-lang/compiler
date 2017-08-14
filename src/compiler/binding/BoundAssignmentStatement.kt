package compiler.binding

import compiler.InternalCompilerError
import compiler.ast.AssignmentStatement
import compiler.ast.Executable
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.nullableOr
import compiler.parser.Reporting

class BoundAssignmentStatement(
    override val context: CTContext,
    override val declaration: AssignmentStatement,
    val targetExpression: BoundExpression<*>,
    val valueExpression: BoundExpression<*>
) : BoundExecutable<AssignmentStatement> {

    /**
     * What this statement assigns to. Must not be null after semantic analysis has been completed.
     */
    var assignmentTargetType: AssignmentTargetType? = null
        private set

    /**
     * The variable this statement assigns to, if it does assign to a variable (see [assignmentTargetType])
     */
    var targetVariable: BoundVariable? = null
        private set

    override val isGuaranteedToThrow: Boolean?
        get() = targetExpression.isGuaranteedToThrow nullableOr valueExpression.isGuaranteedToThrow

    override fun semanticAnalysisPhase1() = targetExpression.semanticAnalysisPhase1() + valueExpression.semanticAnalysisPhase1()

    override fun semanticAnalysisPhase2() = targetExpression.semanticAnalysisPhase2() + valueExpression.semanticAnalysisPhase2()

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // TODO
        // reject if the targetExpression does not point to something that
        // can or should be written to
        if (targetExpression is BoundIdentifierExpression) {
            reportings.addAll(targetExpression.semanticAnalysisPhase3())
            if (targetExpression.referredType == BoundIdentifierExpression.ReferredType.VARIABLE) {
                assignmentTargetType = AssignmentTargetType.VARIABLE
                targetVariable = targetExpression.referredVariable!!

                if (!targetVariable!!.isAssignable) {
                    reportings.add(Reporting.error("Cannot assign to value / final variable ${targetVariable!!.name}", declaration.sourceLocation))
                }
            }
            else {
                reportings += Reporting.error("Cannot assign a value to a type", declaration.sourceLocation)
            }
        }
        else if (targetExpression is BoundMemberAccessExpression) {
        }
        else {
            reportings += Reporting.error("Cannot assign to this target", declaration.targetExpression.sourceLocation)
        }

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return valueExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        val writesByValueExpression = valueExpression.findWritesBeyond(boundary)

        if (assignmentTargetType == AssignmentTargetType.VARIABLE) {
            // check whether the target variable is beyond the boundary
            if (context.containsWithinBoundary(targetVariable!!, boundary)) {
                return writesByValueExpression
            }
            else {
                return writesByValueExpression + this
            }
        }
        else {
            throw InternalCompilerError("Write boundary check for $assignmentTargetType not implemented yet")
        }
    }

    enum class AssignmentTargetType {
        VARIABLE,
        OBJECT_MEMBER
    }
}