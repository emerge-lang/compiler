package compiler.parser.grammar.rule

/**
 * A placeholder for a matching token, e.g. an identifier, an operator, ...
 *
 * When implementing this interface for a singular token (e.g. [GrammarReceiver.identifier]) you
 * likely don't need to implement any of the methods. A good [toString] greatly helps debugging!
 *
 * If your implementation wraps another instance of [ExpectedToken] you need to be very careful with which
 * methods you override and how you do it. At least [markAsRemovingAmbiguity] and [unwrap] are a necessity then,
 * and [toString] should delegate to the wrapped instance.
 */
interface ExpectedToken {
    /**
     * Called on the first [ExpectedToken] in a sequence returned from [Rule.minimalMatchingSequence]
     * which is unique among the other options (see e.g. [EitherOfRule]). By consequence, once this
     * token is matched in any invocation of [Rule.match], the [MatchingResult.isAmbiguous] returned
     * from then on must be `true`.
     * All of that is scoped to each unique context ([inContext]).
     */
    fun markAsRemovingAmbiguity(inContext: MatchingContext) {}

    /**
     * @return an [ExpectedToken] that directly models an expected token, rather than delegating/wrapping
     * another [ExpectedToken] instance. May return itself if that's already the case.
     */
    fun unwrap(): ExpectedToken = this

    /**
     * @return true Iff a [Token] exists that would match both `this` and [other].
     */
    fun couldMatchSameTokenAs(other: ExpectedToken): Boolean = unwrap().couldMatchSameTokenAs(other.unwrap())

    /**
     * has the same contract as [Any.equals].
     *
     * `a.isCloneOf(b)` implies `a.couldMatchSameTokenAs(b)`
     *
     * @return whether [this] and [other] refer to the same original token in the same grammar, through the
     * same route. `a.isCloneOf(b) && a !== b` happens to tokens preceding an [EitherOfRule] in a [SequenceRule].
     */
    fun isCloneOf(other: ExpectedToken): Boolean = this === other
}