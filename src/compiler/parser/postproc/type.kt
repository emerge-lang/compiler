/**
 *
 */
package compiler.parser.postproc

import compiler.ast.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun TypePostprocessor(rule: Rule<List<MatchingResult<*>>>): Rule<TypeReference> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): TypeReference {
    val nameToken = tokens.next()!! as IdentifierToken

    val isNullable = tokens.hasNext() && tokens.next()!! == OperatorToken(Operator.QUESTION_MARK)

    return TypeReference(nameToken, isNullable)
}