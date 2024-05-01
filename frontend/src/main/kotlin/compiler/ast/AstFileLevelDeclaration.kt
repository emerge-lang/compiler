package compiler.ast

import compiler.lexer.Span

interface AstFileLevelDeclaration {
    val declaredAt: Span
}