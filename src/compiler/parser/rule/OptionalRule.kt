package compiler.parser.rule

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence

class OptionalRule<T>(
        val subRule: Rule<T>
): Rule<T?>
{
    override val descriptionOfAMatchingThing: String
        get() = "optional " + subRule.descriptionOfAMatchingThing

    override fun tryMatch(input: TokenSequence): MatchingResult<T?> {
        val subResult = subRule.tryMatch(input)

        if (subResult.certainty == ResultCertainty.DEFINITIVE || subResult.isSuccess) {
            return MatchingResult(
                ResultCertainty.DEFINITIVE,
                subResult.result,
                subResult.errors
            )
        }
        else  {
            return MatchingResult(
                ResultCertainty.OPTIMISTIC,
                null,
                emptySet()
            )
        }
    }
}
