package compiler.reportings

import compiler.binding.BoundFunction
import compiler.binding.BoundMemberFunction
import compiler.lexer.SourceLocation

data class OverrideAddsSideEffectsReporting(
    val override: BoundMemberFunction,
    val superFunction: BoundMemberFunction,
) : Reporting(
    Level.ERROR,
    "The purity of overrides must be compatible with that of the overridden function. ${override.purity} is not a subset of ${superFunction.purity}",
    override.declaredAt,
) {
    override fun toString(): String {
        var str = "${levelAndMessage}\n"
        str += illustrateHints(
            SourceHint(superFunction.purityDeclarationLocation, "overridden function is ${superFunction.purity}"),
            SourceHint(override.purityDeclarationLocation, "override is ${override.purity}"),
        )
        return str
    }
}

private val BoundFunction.purityDeclarationLocation: SourceLocation
    get() = attributes.purityAttribute?.sourceLocation ?: declaredAt