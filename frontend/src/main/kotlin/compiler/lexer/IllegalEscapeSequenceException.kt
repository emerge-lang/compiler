package compiler.lexer

class IllegalEscapeSequenceException(
    val location: Span,
    message: String,
    cause: Throwable? = null,
) : RuntimeException(message, cause)