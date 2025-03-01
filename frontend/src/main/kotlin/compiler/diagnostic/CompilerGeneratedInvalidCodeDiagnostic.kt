package compiler.diagnostic

import compiler.lexer.Span

class CompilerGeneratedInvalidCodeDiagnostic : Diagnostic(
    Severity.ERROR,
    """
        The compiler generated code that didn't pass semantic validation. This is very likely a bug in the compiler.
        The following errors are from this generated code.
    """.trimIndent(),
    Span.UNKNOWN,
) {
    override fun toString() = levelAndMessage
}