package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.lexer.OperatorToken
import compiler.lexer.Token
import compiler.parser.Reporting
import compiler.parser.TokenSequence
import compiler.parser.rule.MatchingResult
import compiler.parser.rule.Rule
import java.util.*

/**
 * Maps all the emitted [MatchingResult]s of the receiver [Rule] that are SUCCESSes using the given `mapper`; passes
 * on error results with null results
 */
fun <B,A> Rule<B>.map(mapper: (MatchingResult<B>) -> MatchingResult<A>): Rule<A> {

    val base = this

    return object: Rule<A> {
        override val descriptionOfAMatchingThing: String = base.descriptionOfAMatchingThing

        override fun tryMatch(input: TokenSequence): MatchingResult<A> {
            val baseResult = base.tryMatch(input)

            if (baseResult.isSuccess) {
                return mapper(baseResult)
            }
            else {
                if (baseResult.result == null) {
                    // we can cast, null has any type you make it be
                    return baseResult as MatchingResult<A>
                }
                else {
                    throw InternalCompilerError("Encountered non-success compiler.matching result with non-null result; cannot map type-safely.");
                }
            }
        }
    }
}

/**
 * Like map, but requires the mapper to act on the results only
 */
fun <B,A> Rule<B>.mapResult(mapper: (B) -> A): Rule<A> = map {
    MatchingResult(
        it.certainty,
        mapper(it.result!!),
        it.errors
    )
}

/**
 * Assumes that the Rule never returns anything but [Token]s and collections of [Token]s. Flattens all these tokens
 * into a single [TokenSequence] and returns that as the compiler.matching result.
 * Also, collects all the reportings into one flat structure
 */
fun Rule<*>.collectTokens(): Rule<TokenSequence> {
    return map { base ->
        val tokenBucket: MutableList<Token> = LinkedList()
        val reportingsBucket: MutableSet<Reporting> = HashSet()

        fun collectFrom(item: Any?) {
            if (item is Token) {
                tokenBucket.add(item)
            }
            else if (item is MatchingResult<*>) {
                collectFrom(item.result)
                collectFrom(item.errors)
            }
            else if (item is Collection<*>) {
                for (subResult in item) {
                    collectFrom(subResult)
                }
            }
            else if (item is Reporting) {
                reportingsBucket.add(item)
            }
            else {
                throw IllegalArgumentException("Unexpected return value in nested structure $item; expected only Token, Collection<Token>, MatchingResult<recursive>")
            }
        }

        collectFrom(base)

        return@map MatchingResult(
            base.certainty,
            TokenSequence(tokenBucket),
            reportingsBucket
        )
    }
}

fun Rule<TokenSequence>.trimWhitespace(front: Boolean = true, back: Boolean = true): Rule<TokenSequence> {
    val isWhitespace: (Token) -> Boolean = { OperatorToken(compiler.lexer.Operator.NEWLINE) == it }

    return this.mapResult { tokens ->
        val tokenList = tokens.remainingToList()

        if (front) tokenList.dropWhile(isWhitespace)
        if (back) tokenList.dropLastWhile(isWhitespace)

        return@mapResult TokenSequence(tokenList)
    }
}

/**
 * Operates on all [MatchingResult]s emitted by the receiver rule.
 * Runs all [Reporting]s of the receiver that have a level of [Reporting.Level.ERROR] or higher and are matched by the
 * given `predicate` through the `enhance` function; the [Reporting]s passed into `enhance` are not returned.
 */
fun <T> Rule<T>.enhanceErrors(predicate: (Reporting) -> Boolean, enhance: (Reporting) -> Reporting): Rule<T> {

    val enhancerMapper: (Reporting) -> Reporting = { reporting ->
        if (reporting.level >= Reporting.Level.ERROR && predicate(reporting))
            enhance(reporting)
        else reporting
    }

    val base = this

    return object: Rule<T> {
        override val descriptionOfAMatchingThing: String = base.descriptionOfAMatchingThing

        override fun tryMatch(input: TokenSequence): MatchingResult<T> {
            val baseResult = base.tryMatch(input)

            if (baseResult.errors.isEmpty()) {
                return baseResult
            }
            else {
                return MatchingResult(
                        baseResult.certainty,
                        baseResult.result,
                        baseResult.errors.map(enhancerMapper).toSet()
                )
            }
        }
    }
}