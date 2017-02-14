package parser.rule

import parser.rule.MatchingResult
import parser.Reporting
import matching.ResultCertainty

class SimpleMatchingResult<ResultType>(
        override val certainty: ResultCertainty,
        override val result: ResultType?,
        vararg reportings: Reporting
) : MatchingResult<ResultType>
{
    override val errors: Set<Reporting> = reportings.toSet()
}