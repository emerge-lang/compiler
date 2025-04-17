package compiler.binding.impurity

import compiler.binding.BoundVariableAssignmentStatement
import compiler.lexer.Span

interface ReassignmentBeyondBoundary : Impurity {
    data class Variable(val assignment: BoundVariableAssignmentStatement) : ReassignmentBeyondBoundary {
        override val span = assignment.variableName.span
        override val kind = Impurity.ActionKind.MODIFY
        override fun describe(): String = "assigning a new value to ${assignment.variableName.value}"
    }
    data class MemberVariable(val memberVariableName: String, override val span: Span) : ReassignmentBeyondBoundary {
        override val kind = Impurity.ActionKind.MODIFY
        override fun describe(): String = "assigning a value to member variable `${memberVariableName}`"
    }
}