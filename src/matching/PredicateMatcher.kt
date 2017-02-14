package matching

open class PredicateMatcher<SubjectType,ErrorType>(
        private val predicate: (SubjectType) -> Boolean,
        override val descriptionOfAMatchingThing: String,
        private val mismatchDescription: (SubjectType) -> ErrorType
) : Matcher<SubjectType, SubjectType, ErrorType>
{
    override fun tryMatch(thing: SubjectType): AbstractMatchingResult<SubjectType, ErrorType>
    {
        if (predicate(thing))
        {
            return AbstractMatchingResult.ofResult(thing)
        }
        else
        {
            return AbstractMatchingResult.ofError(describeMismatchOf(thing))
        }
    }

    open operator fun invoke(thing: SubjectType): Boolean = predicate(thing)

    override fun describeMismatchOf(seq: SubjectType): ErrorType = mismatchDescription(seq)
}