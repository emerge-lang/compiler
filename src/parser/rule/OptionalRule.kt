package parser.rule

import matching.ResultCertainty
import parser.TokenSequence

class OptionalRule<T>(
        val subRule: Rule<T>
): Rule<T?>
{
    override val descriptionOfAMatchingThing: String
        get() = "optional " + subRule.descriptionOfAMatchingThing

    override fun tryMatch(input: TokenSequence): MatchingResult<T?> {
        val subResult = subRule.tryMatch(input)
        return MatchingResult(
                ResultCertainty.OPTIMISTIC,
                subResult.result,
                subResult.errors
        )
    }
}
