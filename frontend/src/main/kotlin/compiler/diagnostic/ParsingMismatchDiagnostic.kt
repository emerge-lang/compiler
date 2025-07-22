package compiler.diagnostic

import compiler.diagnostic.rendering.CellBuilder
import compiler.lexer.Token

class ParsingMismatchDiagnostic(
    val expectedAlternatives: Collection<String>,
    val actual: Token,
) : Diagnostic(
    Severity.ERROR,
    "<mismatch>",
    actual.span
) {
    context(CellBuilder)
    override fun renderMessage() {
        val uniqueAlternatives = expectedAlternatives.toSet()
        val expectedFirstPart = uniqueAlternatives.singleOrNull() ?: "either of:"
        text("Unexpected ${actual.toStringWithoutLocation()}, expected $expectedFirstPart")
        uniqueAlternatives
            .takeIf { it.size > 1 }
            ?.forEach {
                assureOnBlankLine()
                text("- $it")
            }
    }
}