package compiler

class InternalCompilerError(msg: String?, cause: Throwable? = null) : RuntimeException(msg, cause)