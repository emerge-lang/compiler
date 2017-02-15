package matching

interface AbstractMatchingResult<out ResultType,ErrorType> {
    val certainty: ResultCertainty
    val result: ResultType?
    val errors: Set<ErrorType>

    val isError: Boolean

    companion object {
        fun <ResultType, ErrorType> ofResult(result: ResultType, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ResultType, ErrorType> {
            return object : AbstractMatchingResult<ResultType, ErrorType> {
                override val certainty = certainty
                override val result = result
                override val errors = emptySet<ErrorType>()
                override val isError = false
            }
        }

        fun <ResultType, ErrorType> ofError(error: ErrorType, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ResultType, ErrorType> {
            return object : AbstractMatchingResult<ResultType, ErrorType> {
                override val certainty = certainty
                override val result = null
                override val errors = setOf(error)
                override val isError = true
            }
        }

        inline fun <T, reified ResultType, reified ErrorType> of(thing: T, certainty: ResultCertainty = ResultCertainty.DEFINITIVE): AbstractMatchingResult<ResultType, ErrorType> {
            if (thing is ResultType) return ofResult(thing, certainty)
            if (thing is ErrorType) return ofError(thing, certainty)
            throw IllegalArgumentException("Given object is neither of result type nor of error type")
        }
    }
}