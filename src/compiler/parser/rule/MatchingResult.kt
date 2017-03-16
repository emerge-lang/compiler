package compiler.parser.rule

import compiler.matching.AbstractMatchingResult
import compiler.matching.ResultCertainty
import compiler.parser.Reporting

open class MatchingResult<out ResultType>(
        override val certainty: ResultCertainty,
        override val result: ResultType?,
        override val reportings: Set<Reporting>
) : AbstractMatchingResult<ResultType, Reporting>
{
    open override val isError: Boolean
        get() = (reportings.max()?.level ?: Reporting.Level.values().min()!!) >= Reporting.Level.ERROR

    open val isSuccess: Boolean
        get() = !isError && result != null
}