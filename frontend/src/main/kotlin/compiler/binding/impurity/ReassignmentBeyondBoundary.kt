package compiler.binding.impurity

import compiler.binding.BoundVariableAssignmentStatement
import compiler.binding.expression.BoundExpression

interface ReassignmentBeyondBoundary : Impurity {
    data class Variable(val assignment: BoundVariableAssignmentStatement) : ReassignmentBeyondBoundary {
        override val span = assignment.variableName.span
        override val kind = Impurity.ActionKind.MODIFY
        override fun describe(): String = "assigning a new value to ${assignment.variableName.value}"
    }
    data class Complex(val assignmentTarget: BoundExpression<*>) : ReassignmentBeyondBoundary {
        override val span = assignmentTarget.declaration.span
        override val kind = Impurity.ActionKind.MODIFY
        override fun describe(): String = "assigning a new value to this target"
    }
}