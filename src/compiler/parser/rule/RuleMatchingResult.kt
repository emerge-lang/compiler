package compiler.parser.rule

import compiler.matching.AbstractMatchingResult
import compiler.matching.ResultCertainty
import compiler.matching.SimpleMatchingResult
import compiler.parser.Reporting

typealias RuleMatchingResult<ResultType> = AbstractMatchingResult<ResultType, Reporting>

class RuleMatchingResultImpl<ResultType>(
        certainty: ResultCertainty,
        item: ResultType?,
        reportings: Collection<Reporting>
) : SimpleMatchingResult<ResultType, Reporting>(
        certainty,
        item,
        reportings
)