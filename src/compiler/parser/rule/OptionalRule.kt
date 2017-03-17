package compiler.parser.rule

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence

class OptionalRule<T>(
        val subRule: Rule<T>
): Rule<T?>
{
    override val descriptionOfAMatchingThing: String
        get() = "optional " + subRule.descriptionOfAMatchingThing

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<T?> {
        val subResult = subRule.tryMatch(input)

        if (subResult.item == null) {
            if (subResult.certainty == ResultCertainty.DEFINITIVE) {
                return RuleMatchingResultImpl(
                    ResultCertainty.NOT_RECOGNIZED,
                    subResult.item,
                    subResult.reportings
                )
            }
        }

        return subResult
    }
}
