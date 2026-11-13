package compiler.diagnostic

import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.EmergeConstants

class UniqueClassConstructorInvocationDiagnostic(
    val className: String,
    span: Span,
) : Diagnostic(
    Severity.ERROR,
    "$className is a unique class, its constructor cannot be invoked. Obtain the instance with $className.${EmergeConstants.UNIQUE_CLASS_TAKE_FUNCTION_NAME}",
    span,
)
