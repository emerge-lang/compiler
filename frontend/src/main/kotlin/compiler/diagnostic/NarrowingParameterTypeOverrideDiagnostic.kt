package compiler.diagnostic

import compiler.binding.BoundParameter
import compiler.diagnostic.rendering.CellBuilder

class NarrowingParameterTypeOverrideDiagnostic(
    val override: BoundParameter,
    val superParameter: BoundParameter,
    val assignabilityError: ValueNotAssignableDiagnostic,
) : Diagnostic(
    Severity.ERROR,
    "Cannot narrow type of overridden parameter ${override.name}; ${assignabilityError.reason}",
    assignabilityError.span,
) {
    context(builder: CellBuilder)
    override fun renderBody() {
        builder.sourceHints(
            SourceHint(
                superParameter.declaration.type?.span ?: superParameter.declaration.span,
                "overridden function establishes the type ${assignabilityError.sourceType.quote()}",
                severity = Severity.INFO
            ),
            SourceHint(
                assignabilityError.targetType.span ?: override.declaration.span,
                "overriding function requires are more specific type",
                severity = severity
            ),
        )
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