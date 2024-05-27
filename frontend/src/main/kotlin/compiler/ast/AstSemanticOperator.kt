package compiler.ast

import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.OperatorToken
import compiler.lexer.Token

/**
 * An unary or binary operator, which can syntactically be an [OperatorToken] but also a [KeywordToken],
 * e.g. [Keyword.AND].
 */
class AstSemanticOperator private constructor(
    val token: Token,
    /** The [Operator] or [Keyword] */
    val operatorElement: Any,
    val name: String,
) {
    constructor(token: KeywordToken) : this(token, token.keyword, token.keyword.name)
    constructor(token: OperatorToken) : this(token, token.operator, token.operator.text)
}