package compiler.ast

import compiler.lexer.Span

sealed interface Executable {
    val span: Span
}