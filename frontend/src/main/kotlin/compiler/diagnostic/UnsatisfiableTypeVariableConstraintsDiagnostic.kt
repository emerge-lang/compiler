package compiler.diagnostic

import compiler.ast.type.TypeParameter
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.TypeUnification
import compiler.lexer.Span

class UnsatisfiableTypeVariableConstraintsDiagnostic private constructor (
    val parameter: TypeParameter,
    upperBoundBeforeProblem: BoundTypeReference,
    lowerBoundBeforeProblem: BoundTypeReference,
    incompatibleExtraConstraint: String,
    inferenceLocation: Span,
) : Diagnostic(
    Severity.ERROR,
    """
        There is no value for type variable ${parameter.name.value} such that all constraints can be satisfied.
        
        Constraints:
        ${parameter.name.value} : $upperBoundBeforeProblem
        $lowerBoundBeforeProblem : ${parameter.name.value}
        $incompatibleExtraConstraint
    """.trimIndent(),
    inferenceLocation,
) {
    override fun toString() = "$levelAndMessage\n${illustrateHints(
        SourceHint(span, "constraints become unsatisfiable here"),
        SourceHint(parameter.name.span, "this parameter is affected"),
    )}"

    override fun equals(other: Any?): Boolean {
        if (other !is UnsatisfiableTypeVariableConstraintsDiagnostic) return false
        if (this.span != other.span) return false
        if (this.parameter != other.parameter) return false

        return true
    }

    override fun hashCode(): Int {
        var result = span.hashCode()
        result = 31 * result + parameter.hashCode()

        return result
    }

    companion object {
        fun forSupertypeConstraint(
            parameter: BoundTypeParameter,
            atState: TypeUnification.VariableState,
            lowerBound: BoundTypeReference,
            inferenceLocation: Span,
        ): UnsatisfiableTypeVariableConstraintsDiagnostic {
            return UnsatisfiableTypeVariableConstraintsDiagnostic(
                parameter.astNode,
                atState.upperBound,
                atState.lowerBound,
                "$lowerBound : ${parameter.name}",
                inferenceLocation,
            )
        }

        fun forSubtypeConstraint(
            parameter: BoundTypeParameter,
            atState: TypeUnification.VariableState,
            upperBound: BoundTypeReference,
            inferenceLocation: Span,
        ): UnsatisfiableTypeVariableConstraintsDiagnostic {
            return UnsatisfiableTypeVariableConstraintsDiagnostic(
                parameter.astNode,
                atState.upperBound,
                atState.lowerBound,
                "${parameter.name} : $upperBound",
                inferenceLocation,
            )
        }
    }
}