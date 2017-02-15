package compiler.parser.grammar

import compiler.parser.rule.MatchingResult
import compiler.parser.rule.*

fun rule(initFn: DSLFixedSequenceRule.() -> Any?): Rule<List<MatchingResult<*>>> {
    val rule = DSLFixedSequenceRule()
    rule.initFn()

    return rule
}

fun <ResultBefore,ResultAfter> Rule<ResultBefore>.postprocess(postProcessor: (Rule<ResultBefore>) -> Rule<ResultAfter>): Rule<ResultAfter>
    = postProcessor(this)