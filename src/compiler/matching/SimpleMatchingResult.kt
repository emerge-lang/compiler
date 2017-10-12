package compiler.matching

open class SimpleMatchingResult<ResultType, ReportingType>(
        override val certainty: ResultCertainty,
        override val item: ResultType?,
        override val reportings: Collection<ReportingType>
) : AbstractMatchingResult<ResultType, ReportingType> {
    constructor(certainty: ResultCertainty, item: ResultType?, vararg reportings: ReportingType) : this(certainty, item, reportings.toSet())

    init {
        if (item == null && reportings.isEmpty()) {
            //throw InternalCompilerError("When the item is null there must be reportings. Use Unit to resemble meaningless matches.")
        }
    }
}