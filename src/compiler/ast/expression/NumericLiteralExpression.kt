package compiler.ast.expression

import compiler.ast.type.BaseType
import compiler.lexer.NumericLiteralToken

class NumericLiteralExpression(val literalToken: NumericLiteralToken, val baseType: BaseType) : Expression {
    override val type = baseType.defaultReference
}