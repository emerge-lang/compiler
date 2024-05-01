package compiler.reportings

import compiler.lexer.Token

class ParsingMismatchReporting(
    val expectedAlternatives: Collection<String>,
    val actual: Token,
) : Reporting(
    Level.ERROR,
    "<mismatch>",
    actual.span
) {
    override val message: String by lazy {
        val uniqueAlternatives = expectedAlternatives.toSet()
        val expectedDesc = uniqueAlternatives.singleOrNull() ?: uniqueAlternatives.joinToString(
            prefix = "either of:\n",
            transform = { "  - $it" },
            separator = "\n",
        )
        "Unexpected ${actual.toStringWithoutLocation()}, expected $expectedDesc"
    }
}