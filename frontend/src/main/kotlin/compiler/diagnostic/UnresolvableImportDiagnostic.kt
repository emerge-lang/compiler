package compiler.diagnostic

import compiler.lexer.IdentifierToken
import io.github.tmarsteel.emerge.common.CanonicalElementName

data class UnresolvableImportDiagnostic(
    val packageName: CanonicalElementName.Package,
    val symbol: IdentifierToken,
) : Diagnostic(
    Severity.ERROR,
    "Could not find a function, type or variable with the name ${symbol.quote()} in package ${packageName.quote()}",
    symbol.span,
) {
    override fun toString() = super.toString()
}