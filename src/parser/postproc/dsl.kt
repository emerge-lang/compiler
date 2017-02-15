package parser.postproc

import parser.Reporting
import parser.TokenSequence
import parser.rule.MatchingResult
import parser.rule.Rule

fun <T> Rule<T>.enhanceErrors(predicate: (Reporting) -> Boolean, enhance: (Reporting) -> Reporting): Rule<T> {

    val enhancerMapper: (Reporting) -> Reporting = { reporting ->
        if (reporting.level >= Reporting.Level.ERROR && predicate(reporting))
            enhance(reporting)
        else reporting
    }

    val base = this

    return object: Rule<T> {
        override val descriptionOfAMatchingThing: String = base.descriptionOfAMatchingThing

        override fun tryMatch(input: TokenSequence): MatchingResult<T> {
            val baseResult = base.tryMatch(input)

            if (baseResult.errors.isEmpty()) {
                return baseResult
            }
            else {
                return MatchingResult(
                        baseResult.certainty,
                        baseResult.result,
                        baseResult.errors.map(enhancerMapper).toSet()
                )
            }
        }
    }
}