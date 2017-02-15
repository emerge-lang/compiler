package compiler.parser.rule

import compiler.parser.Reporting
import compiler.matching.ResultCertainty

class SimpleMatchingResult<ResultType>(
        certainty: ResultCertainty,
        result: ResultType?,
        vararg reportings: Reporting
) : MatchingResult<ResultType>(certainty, result, reportings.toSet())