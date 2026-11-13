package compiler.diagnostic

import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.EmergeConstants

class ReservedIdentifierDiagnostic(
    val identifier: String,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "Identifiers starting with ${EmergeConstants.COMPILER_INTERNAL_IDENTIFIER_PREFIX} are reserved for the compiler",
    span,
)
