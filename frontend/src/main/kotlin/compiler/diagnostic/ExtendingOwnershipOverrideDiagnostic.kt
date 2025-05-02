package compiler.diagnostic

import compiler.binding.BoundParameter
import compiler.lexer.Span

class ExtendingOwnershipOverrideDiagnostic(
    val override: BoundParameter,
    val superParameter: BoundParameter,
) : Diagnostic(
    Severity.ERROR,
    "Cannot extend ownership of parameter ${override.name}",
    override.declaration.span,
) {
    override fun toString(): String {
        var str = "${levelAndMessage}\n"
        str += illustrateHints(
            SourceHint(superParameter.ownershipSpan, "overridden function borrows the parameter"),
            SourceHint(override.ownershipSpan, "override cannot capture it"),
        )
        return str
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ExtendingOwnershipOverrideDiagnostic) return false
        if (!super.equals(other)) return false

        if (override.declaration.span != other.override.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        var result = super.hashCode()
        result = 31 * result + override.declaration.span.hashCode()
        return result
    }
}

private val BoundParameter.ownershipSpan: Span
    get() = declaration.ownership?.second?.span ?: declaration.span