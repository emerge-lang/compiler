package compiler.ast.expression

import compiler.lexer.IdentifierToken

/** A expression that evaluates using an identigier (variable reference)  */
class IdentifierExpression(val identifier: IdentifierToken) : Expression {
    override val sourceLocation = identifier.sourceLocation
}