package parser.rule

import matching.AbstractMatchingResult
import parser.Reporting
import parser.TokenSequence

/**
 * Matches the first of any given sub-rule
 */
open class FirstOfRule(
        subRules: Collection<Rule<*>>
) : Rule<Any>
{
    override val descriptionOfAMatchingThing: String
        get() = throw UnsupportedOperationException()

    override fun tryMatch(input: TokenSequence): AbstractMatchingResult<Any, Reporting> {
        throw UnsupportedOperationException("not implemented") // TODO: implement
    }
}
