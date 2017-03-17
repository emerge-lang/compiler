package compiler.parser.postproc

import compiler.ast.expression.NumericLiteralExpression
import compiler.lexer.NumericLiteralToken
import compiler.matching.ResultCertainty
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun NumericLiteralPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<NumericLiteralExpression> {
    return rule
        .flatten()
        .map(::toAST)
}

private fun toAST(matchingResult: RuleMatchingResult<TransactionalSequence<Any, Position>>): RuleMatchingResult<NumericLiteralExpression> {
    val numericToken = matchingResult.item?.next()!! as NumericLiteralToken

    return RuleMatchingResultImpl(
        ResultCertainty.DEFINITIVE,
        NumericLiteralExpression(numericToken),
        emptySet()
    )
}