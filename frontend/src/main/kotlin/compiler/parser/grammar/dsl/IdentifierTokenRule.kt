package compiler.parser.grammar.dsl

import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.grammar.rule.SingleTokenRule

class IdentifierTokenRule(
    val acceptedOperators: Set<Operator>,
    val acceptedKeywords: Set<Keyword>,
) : SingleTokenRule<IdentifierToken>("an identifier", { token -> when(token) {
    is IdentifierToken -> token
    is OperatorToken -> if (token.operator in acceptedOperators) {
        IdentifierToken(token.operator.text, token.sourceLocation)
    } else null
    is KeywordToken -> if (token.keyword in acceptedKeywords) {
        IdentifierToken(token.sourceText, token.sourceLocation)
    } else null
    else -> null
} })