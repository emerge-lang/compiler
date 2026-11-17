package compiler.diagnostic

import compiler.ast.type.AstSimpleTypeReference
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeParameter
import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Span

/**
 * A member function that doesn't declare a receiver refers to a type parameter of its base type.
 */
class TypeParameterUnavailableWithoutReceiverDiagnostic(
    val reference: AstSimpleTypeReference,
    val parameter: TypeParameter,
) : Diagnostic(
    Severity.ERROR,
    "Type parameter ${parameter.name.value} is not available here, because this function doesn't have a receiver. The type arguments of a type belong to its objects; declare a `self` parameter, or a type parameter on the function.",
    (reference as? NamedTypeReference)?.declaringNameToken?.span ?: reference.span ?: Span.UNKNOWN,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        builder.sourceHints(
            SourceHint(parameter.name.span, "${parameter.name.value} is declared here, on the type"),
            SourceHint(span, "there is no object to take ${parameter.name.value} from", severity = severity),
        )
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is TypeParameterUnavailableWithoutReceiverDiagnostic) return false

        return reference == other.reference
    }

    override fun hashCode(): Int {
        return reference.hashCode()
    }
}
