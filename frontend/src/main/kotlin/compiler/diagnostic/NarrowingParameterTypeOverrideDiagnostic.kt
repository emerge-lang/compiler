package compiler.diagnostic

import compiler.binding.BoundParameter

class NarrowingParameterTypeOverrideDiagnostic(
    val override: BoundParameter,
    val superParameter: BoundParameter,
    val assignabilityError: ValueNotAssignableDiagnostic,
) : Diagnostic(
    Severity.ERROR,
    "Cannot narrow type of overridden parameter ${override.name}; ${assignabilityError.reason}",
    assignabilityError.span,
) {
    override fun toString(): String {
        var str = "${levelAndMessage}\n"
        str += illustrateHints(
            SourceHint(superParameter.declaration.type?.span ?: superParameter.declaration.span, "overridden function establishes the type ${assignabilityError.sourceType}"),
            SourceHint(assignabilityError.targetType.span ?: override.declaration.span, "overriding function requires are more specific type"),
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