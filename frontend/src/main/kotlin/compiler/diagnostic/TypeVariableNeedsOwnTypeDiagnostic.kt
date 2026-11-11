package compiler.diagnostic

import compiler.ast.type.TypeParameter
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Span

/**
 * @see OwnTypeArgumentDiagnostic
 */
class TypeVariableNeedsOwnTypeDiagnostic(
    val parameter: TypeParameter,
    inferenceLocation: Span,
) : Diagnostic(
    Severity.ERROR,
    "Cannot infer a type argument for `${parameter.name.value}`: the constraints on it ask for both a mut and a const type, which only a type of the mutability own fits; and type arguments cannot be of the mutability own.",
    inferenceLocation,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        builder.sourceHints(
            SourceHint(span, "inferred here", severity = severity),
            SourceHint(parameter.name.span, "this parameter is affected", severity = Severity.INFO),
        )
    }

    override fun equals(other: Any?): Boolean {
        if (other !is TypeVariableNeedsOwnTypeDiagnostic) return false
        if (this.span != other.span) return false
        if (this.parameter != other.parameter) return false

        return true
    }

    override fun hashCode(): Int {
        var result = span.hashCode()
        result = 31 * result + parameter.hashCode()
        return result
    }
}
