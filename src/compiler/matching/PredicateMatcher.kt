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
            return AbstractMatchingResult.ofResult(input)
        }
        else
        {
            return AbstractMatchingResult.ofError(describeMismatchOf(input))
        }
    }

    open operator fun invoke(thing: SubjectType): Boolean = predicate(thing)

    override fun describeMismatchOf(seq: SubjectType): ErrorType = mismatchDescription(seq)
}