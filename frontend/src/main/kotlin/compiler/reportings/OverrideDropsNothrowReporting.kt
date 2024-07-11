package compiler.reportings

import compiler.binding.BoundMemberFunction
import compiler.lexer.Keyword

data class OverrideDropsNothrowReporting(
    val override: BoundMemberFunction,
    val superFunction: BoundMemberFunction,
) : Reporting(
    Level.ERROR,
    "Function ${override.canonicalName} must be declared ${Keyword.NOTHROW.text}, because it is overriding a function that is also declared nothrow.",
    override.declaredAt,
) {
    override fun toString(): String {
        var str = "${levelAndMessage}\n"
        str += illustrateHints(
            SourceHint(override.declaredAt, "override is not declared ${Keyword.NOTHROW.text}"),
            SourceHint(superFunction.attributes.firstNothrowAttribute!!.sourceLocation, "overridden function is declared ${Keyword.NOTHROW.text} here"),
        )
        return str
    }
}