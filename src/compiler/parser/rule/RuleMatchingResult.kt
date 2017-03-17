package compiler.parser.rule

import compiler.matching.AbstractMatchingResult
import compiler.matching.ResultCertainty
import compiler.matching.SimpleMatchingResult
import compiler.parser.Reporting

typealias RuleMatchingResult<ItemType> = AbstractMatchingResult<ItemType, Reporting>

class RuleMatchingResultImpl<ItemType>(
        certainty: ResultCertainty,
        item: ItemType?,
        reportings: Collection<Reporting>
) : SimpleMatchingResult<ItemType, Reporting>(
        certainty,
        item,
        reportings
)