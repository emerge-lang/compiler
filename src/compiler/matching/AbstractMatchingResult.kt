package compiler.matching


/**
 * When a [Matcher] is matched against an input it returns an [AbstractMatchingResult] that describes
 * the outcome of the matching process.
 *
 * If there was no doubt about the input is of the structure the matcher expects the [certainty] must be
 * [ResultCertainty.DEFINITIVE]; if the given input is ambigous (e.g. does not have properties unique to the
 * [Matcher]), the [certainty] should be [ResultCertainty.OPTIMISTIC].
 *
 * Along with the [result] of the match, an [AbstractMatchingResult] can provide the caller with additional reportings
 * about the matched input. If the input did not match the expectations of the [Matcher] that could be details on what
 * expectations were not met.
 */
interface AbstractMatchingResult<out ResultType,ReportingType> {
    val certainty: ResultCertainty
    val result: ResultType?
    val reportings: Set<ReportingType>

    val isError: Boolean

    companion object {
        fun <ResultType, ReportingType> ofResult(result: ResultType, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ResultType, ReportingType> {
            return object : AbstractMatchingResult<ResultType, ReportingType> {
                override val certainty = certainty
                override val result = result
                override val reportings = emptySet<ReportingType>()
                override val isError = false
            }
        }

        fun <ResultType, ReportingType> ofError(error: ReportingType, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ResultType, ReportingType> {
            return object : AbstractMatchingResult<ResultType, ReportingType> {
                override val certainty = certainty
                override val result = null
                override val reportings = setOf(error)
                override val isError = true
            }
        }

        inline fun <T, reified ResultType, reified ReportingType> of(thing: T, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ResultType, ReportingType> {
            if (thing is ResultType) return ofResult(thing, certainty)
            if (thing is ReportingType) return ofError(thing, certainty)
            throw IllegalArgumentException("Given object is neither of result type nor of error type")
        }
    }
}