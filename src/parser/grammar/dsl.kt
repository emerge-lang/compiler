package parser.grammar

import parser.rule.MatchingResult
import parser.rule.*

fun rule(initFn: DSLFixedSequenceRule.() -> Any?): Rule<List<MatchingResult<*>>> {
    val rule = DSLFixedSequenceRule()
    rule.initFn()

    return rule
}