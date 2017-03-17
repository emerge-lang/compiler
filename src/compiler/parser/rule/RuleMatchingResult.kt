package compiler.parser.rule

import compiler.matching.AbstractMatchingResult
import compiler.matching.ResultCertainty
import compiler.matching.SimpleMatchingResult
import compiler.parser.Reporting

typealias RuleMatchingResult<ItemType> = AbstractMatchingResult<ItemType, Reporting>

/** Whether one of the reportings is of level [Reporting.Level.ERROR] or higher */
val RuleMatchingResult<*>.hasErrors: Boolean
    get() = this.reportings.find { it.level >= Reporting.Level.ERROR } != null

class RuleMatchingResultImpl<ItemType>(
        certainty: ResultCertainty,
        item: ItemType?,
        reportings: Collection<Reporting>
) : SimpleMatchingResult<ItemType, Reporting>(
        certainty,
        item,
        reportings
)