package compiler.compiler

import compiler.lexer.EndOfInputToken
import compiler.lexer.Span
import io.mockk.mockk

val MockEOIToken = EndOfInputToken(Span(mockk(), 0u, 0u, 0u, 0u))