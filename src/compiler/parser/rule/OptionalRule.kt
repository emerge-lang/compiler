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

        if (subResult.certainty == ResultCertainty.DEFINITIVE) { // TODO: add || subResult.item == null to condition?
            return RuleMatchingResult(
                ResultCertainty.DEFINITIVE,
                subResult.item,
                subResult.reportings
            )
        }
        else  {
            return RuleMatchingResult(
                ResultCertainty.OPTIMISTIC,
                null,
                emptySet()
            )
        }
    }
}
