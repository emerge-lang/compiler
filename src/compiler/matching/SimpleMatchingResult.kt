package compiler.matching

class SimpleMatchingResult<ResultType, ReportingType>(
        override val certainty: ResultCertainty,
        override val result: ResultType?,
        vararg reportings: ReportingType
) : AbstractMatchingResult<ResultType, ReportingType> {
    override val reportings = reportings.toSet()
}