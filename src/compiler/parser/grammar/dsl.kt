package compiler.parser.grammar

import compiler.parser.TokenSequence
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.*

fun rule(initFn: DSLFixedSequenceRule.() -> Any?): Rule<List<MatchingResult<*>>> {
    val rule = DSLFixedSequenceRule()
    // any rule can be preceeded by whitespace
    rule.optionalWhitespace()

    rule.initFn()

    return rule
}

fun <T> Rule<T>.describeAs(description: String): Rule<T> {
    val base = this
    return object : Rule<T> {
        override val descriptionOfAMatchingThing = description

        override fun tryMatch(input: TokenSequence): MatchingResult<T> {
            return base.tryMatch(input);
        }
    }
}

fun <ResultBefore,ResultAfter> Rule<ResultBefore>.postprocess(postProcessor: (Rule<ResultBefore>) -> Rule<ResultAfter>): Rule<ResultAfter>
    = postProcessor(this)