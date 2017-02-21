package compiler.parser.postproc

import compiler.ast.expression.Expression
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule

fun ExpressionPostProcessor(rule: Rule<List<MatchingResult<*>>>): Rule<Expression> {
    return rule
        .flatten() // TODO: will this be a good idea later on?!
        .mapResult { tokens -> tokens.next()!! as Expression }
}
