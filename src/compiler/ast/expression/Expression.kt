package compiler.ast.expression

import compiler.ast.type.TypeReference

interface Expression {
    val type: TypeReference
}