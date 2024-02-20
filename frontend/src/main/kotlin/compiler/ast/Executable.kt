package compiler.ast

import compiler.lexer.SourceLocation

sealed interface Executable {
    val sourceLocation: SourceLocation
}