package compiler.parser.grammar.dsl

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl

internal fun <T> tryMatchOptional(rule: Rule<T>, input: TokenSequence): RuleMatchingResult<T?> {
    val subResult = rule.tryMatch(input)

    if (subResult.item == null) {
        if (subResult.certainty >= ResultCertainty.MATCHED) {
            return RuleMatchingResultImpl(
                ResultCertainty.NOT_RECOGNIZED,
                subResult.item,
                subResult.reportings
            )
        }
        else {
            return RuleMatchingResultImpl(
                ResultCertainty.NOT_RECOGNIZED,
                null,
                emptySet()
            )
        }
    }

    return subResult
}