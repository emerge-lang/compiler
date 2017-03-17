package compiler.matching

open class PredicateMatcher<SubjectType,ErrorType>(
        private val predicate: (SubjectType) -> Boolean,
        override val descriptionOfAMatchingThing: String,
        private val mismatchDescription: (SubjectType) -> ErrorType
) : Matcher<SubjectType, SubjectType, ErrorType>
{
    override fun tryMatch(input: SubjectType): AbstractMatchingResult<SubjectType, ErrorType>
    {
        if (predicate(input))
        {
            return SimpleMatchingResult(ResultCertainty.DEFINITIVE, input)
        }
        else
        {
            return SimpleMatchingResult(ResultCertainty.DEFINITIVE, null, mismatchDescription(input))
        }
    }

    open operator fun invoke(thing: SubjectType): Boolean = predicate(thing)
}