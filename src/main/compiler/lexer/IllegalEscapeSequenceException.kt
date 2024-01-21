package compiler.lexer

class IllegalEscapeSequenceException(
    val location: SourceLocation,
    message: String,
    cause: Throwable? = null,
) : RuntimeException(message)