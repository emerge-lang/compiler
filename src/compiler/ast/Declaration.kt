package compiler.ast

import compiler.lexer.SourceLocation

interface Declaration {
    val declaredAt: SourceLocation
}