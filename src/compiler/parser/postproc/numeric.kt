package compiler.parser.postproc

import compiler.ast.expression.NumericLiteralExpression
import compiler.lexer.NumericLiteralToken
import compiler.matching.ResultCertainty
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun NumericLiteralPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<NumericLiteralExpression> {
    return rule
        .flatten()
        .map(::toAST)
}

private fun toAST(matchingResult: MatchingResult<TransactionalSequence<Any, Position>>): MatchingResult<NumericLiteralExpression> {
    val numericToken = matchingResult.item?.next()!! as NumericLiteralToken

    return RuleMatchingResult(
        ResultCertainty.DEFINITIVE,
        NumericLiteralExpression(numericToken),
        emptySet()
    )
}