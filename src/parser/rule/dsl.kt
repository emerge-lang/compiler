package parser.rule

import lexer.Token
import parser.Reporting

interface Rule<OutputType> {
    public fun tryMatch(tokens: Sequence<Token>): RuleMatchResult<OutputType>
}

class RuleMatchResult<OutputType>(
    public val result: OutputType?,
    public val reportings: Set<Reporting>
) {
    companion object {
        class Builder<OutputType> {
            private var result: OutputType? = null
            private val reportings: MutableSet<Reporting> = mutableSetOf()

            // TODO: function for error and warning, like builder.warn().setResult()

            public fun setResult(result: OutputType?): Builder<OutputType> {
                this.result = result
                return this
            }

            public fun build(): RuleMatchResult<OutputType> = RuleMatchResult(result, reportings)
        }
    }
}

fun <T> inSequence(rules: Rule<T>): Rule<Sequence<T>> {
    // TODO: Implement
}

fun <T> eitherOf(rules: Rule<T>): Rule<T> {
    // TODO: Implement
}