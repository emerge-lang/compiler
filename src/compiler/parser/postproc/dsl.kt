package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.matching.AbstractMatchingResult
import compiler.matching.SimpleMatchingResult
import compiler.parser.Reporting
import compiler.parser.TokenSequence
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.transact.Position
import compiler.transact.SimpleTransactionalSequence
import compiler.transact.TransactionalSequence
import java.util.*

/**
 * Maps all the emitted [RuleMatchingResult]s of the receiver [Rule] that are SUCCESSes using the given `mapper`; passes
 * on error results with null results
 */
fun <B,A> Rule<B>.map(mapper: (RuleMatchingResult<B>) -> RuleMatchingResult<A>): Rule<A> {

    val base = this

    return object: Rule<A> {
        override val descriptionOfAMatchingThing: String = base.descriptionOfAMatchingThing

        override fun tryMatch(input: TokenSequence): RuleMatchingResult<A> {
            val baseResult = base.tryMatch(input)

            if (baseResult.item == null) {
                @Suppress("UNCHECKED_CAST")
                return baseResult as RuleMatchingResult<A>
            }
            else {
                return mapper(baseResult)
            }
        }
    }
}

/**
 * Like map, but requires the mapper to act on the results only
 */
fun <B,A> Rule<B>.mapResult(mapper: (B) -> A): Rule<A> = map {
    RuleMatchingResultImpl(
        it.certainty,
        if (it.item == null) null else mapper(it.item!!),
        it.reportings
    )
}

/**
 * Flattens all response objects into a single [TransactionalSequence]. Collections and sub-results will be traversed.
 * Also, collects all the reportings into one flat structure
 */
fun Rule<*>.flatten(): Rule<TransactionalSequence<Any, Position>> {
    return map { base ->
        val itemBucket: MutableList<Any> = LinkedList()
        val reportingsBucket: MutableSet<Reporting> = HashSet()

        fun collectFrom(item: Any?) {
            if (item == null || item == Unit) return

            if (item is AbstractMatchingResult<*, *>) {
                collectFrom(item.item)
                collectFrom(item.reportings)
            }
            else if (item is Collection<*>) {
                for (subResult in item) {
                    collectFrom(subResult)
                }
            }
            else if (item is TransactionalSequence<*, *>) {
                itemBucket.addAll(item.remainingToList().filterNotNull())
            }
            else if (item is Reporting) {
                reportingsBucket.add(item)
            }
            else {
                itemBucket.add(item)
            }
        }

        collectFrom(base)

        return@map RuleMatchingResultImpl(
            base.certainty,
            SimpleTransactionalSequence(itemBucket),
            reportingsBucket
        )
    }
}

fun <T> Rule<TransactionalSequence<T, Position>>.trimWhitespaceTokens(front: Boolean = true, back: Boolean = true): Rule<TransactionalSequence<T, Position>> {

    val isWhitespace: (T) -> Boolean = { compiler.parser.isWhitespace(it as Any) }

    return this.mapResult { tokens ->
        val tokenList = tokens.remainingToList()

        if (front) tokenList.dropWhile(isWhitespace)
        if (back) tokenList.dropLastWhile(isWhitespace)

        return@mapResult compiler.transact.SimpleTransactionalSequence(tokenList)
    }
}

/**
 * Operates on all [RuleMatchingResult]s emitted by the receiver rule.
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

        override fun tryMatch(input: TokenSequence): RuleMatchingResult<T> {
            val baseResult = base.tryMatch(input)

            if (baseResult.reportings.isEmpty()) {
                return baseResult
            }
            else {
                return RuleMatchingResultImpl(
                    baseResult.certainty,
                    baseResult.item,
                    baseResult.reportings.map(enhancerMapper).toSet()
                )
            }
        }
    }
}