package compiler.diagnostic

import compiler.lexer.Token

class ParsingMismatchDiagnostic(
    val expectedAlternatives: Collection<String>,
    val actual: Token,
) : Diagnostic(
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