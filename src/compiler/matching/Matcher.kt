package compiler.matching

interface Matcher<SubjectType,ResultType,ErrorType> {
    val descriptionOfAMatchingThing: String
    fun describeMismatchOf(seq: SubjectType): ErrorType

    fun tryMatch(input: SubjectType): AbstractMatchingResult<ResultType,ErrorType>
}