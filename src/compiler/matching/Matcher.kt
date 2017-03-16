package compiler.matching

interface Matcher<SubjectType,ResultType,ErrorType> {
    val descriptionOfAMatchingThing: String

    // TODO: what the heck is this for again?!
    fun describeMismatchOf(seq: SubjectType): ErrorType

    // TODO: define the contract... this method is far too centric to the application to NOT have one
    fun tryMatch(input: SubjectType): AbstractMatchingResult<ResultType,ErrorType>
}