package matching

interface AbstractMatchingResult<ResultType,ErrorType> {
    val certainty: ResultCertainty
    val result: ResultType?
    val errors: Set<ErrorType>

    companion object {
        fun <ResultType, ErrorType> ofResult(result: ResultType, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ResultType, ErrorType> {
            return object : AbstractMatchingResult<ResultType, ErrorType> {
                override val certainty = certainty
                override val result = result
                override val errors = emptySet<ErrorType>()
            }
        }

        fun <ResultType, ErrorType> ofError(error: ErrorType, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ResultType, ErrorType> {
            return object : AbstractMatchingResult<ResultType, ErrorType> {
                override val certainty = certainty
                override val result = null
                override val errors = setOf(error)
            }
        }

        inline fun <T, reified ResultType, reified ErrorType> of(thing: T, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ResultType, ErrorType> {
            if (thing is ResultType) return ofResult(thing, certainty)
            if (thing is ErrorType) return ofError(thing, certainty)
            throw IllegalArgumentException("Given object is neither of result type nor of error type")
        }
    }
}