package parser.rule

import parser.Reporting
import matching.ResultCertainty

class SimpleMatchingResult<ResultType>(
        certainty: ResultCertainty,
        result: ResultType?,
        vararg reportings: Reporting
) : MatchingResult<ResultType>(certainty, result, reportings.toSet())