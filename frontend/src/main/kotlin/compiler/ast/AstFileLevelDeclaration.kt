package compiler.ast

import compiler.lexer.SourceLocation

interface AstFileLevelDeclaration {
    val declaredAt: SourceLocation
}