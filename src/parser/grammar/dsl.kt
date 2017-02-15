package parser.grammar

import parser.rule.MatchingResult
import parser.rule.*

fun rule(initFn: DSLFixedSequenceRule.() -> Any?): Rule<List<MatchingResult<*>>> {
    val rule = DSLFixedSequenceRule()
    rule.initFn()

    return rule
}

fun <ResultBefore,ResultAfter> Rule<ResultBefore>.postprocess(postProcessor: (Rule<ResultBefore>) -> Rule<ResultAfter>): Rule<ResultAfter>
    = postProcessor(this)