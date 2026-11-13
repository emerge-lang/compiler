package compiler.diagnostic

import compiler.lexer.Span

/**
 * Top-level variables are constants: there is no state that every function can reach. State the whole program
 * shares is created in `main` and passed to the code that works with it.
 */
class MutableGlobalVariableDiagnostic(
    val variableName: String,
    reason: String,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "Top-level variable $variableName $reason. Top-level variables are constants; create shared state in the main function and pass it to the code that needs it.",
    span,
)
