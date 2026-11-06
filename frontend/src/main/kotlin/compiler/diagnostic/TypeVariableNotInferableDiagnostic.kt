package compiler.diagnostic

import compiler.ast.type.TypeParameter
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Span

class TypeVariableNotInferableDiagnostic(
    val parameter: TypeParameter,
    inferenceLocation: Span,
) : Diagnostic(
    Severity.ERROR,
    "Cannot infer a type argument for `${parameter.name.value}` because `${parameter.name.value}`s upper bound is self-referential and there is no lower bound for it here. Specify the type arguments explicitly.",
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
        if (other !is TypeVariableNotInferableDiagnostic) return false
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
