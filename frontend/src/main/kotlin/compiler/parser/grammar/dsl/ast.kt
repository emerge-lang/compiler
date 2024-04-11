/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

@file:JvmName("AstDsl")
package compiler.parser.grammar.dsl

import compiler.lexer.EndOfInputToken
import compiler.parser.grammar.rule.MatchingContinuation
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.OngoingMatch
import compiler.parser.grammar.rule.RepeatingRule
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.SequenceRule
import compiler.reportings.ParsingMismatchReporting
import compiler.reportings.Reporting
import compiler.transact.Position
import compiler.transact.SimpleTransactionalSequence
import compiler.transact.TransactionalSequence
import java.util.LinkedList

fun <AstNode : Any> Rule<*>.astTransformation(trimWhitespace: Boolean = false, transformer: (TransactionalSequence<Any, *>) -> AstNode): Rule<AstNode> {
    var mapped = flatten()
    if (trimWhitespace) {
        mapped = mapped.trimWhitespaceTokens()
    }

    return mapped.mapResult(transformer)
}

/**
 * Maps all the emitted [MatchingResult]s of the receiver [Rule] that are SUCCESSes using the given `mapper`; passes
 * on error results with null results
 */
fun <Base : Any, Mapped : Any> Rule<Base>.map(mapper: (MatchingResult<Base>) -> MatchingResult<Mapped>): Rule<Mapped> {
    return object: Rule<Mapped> {
        override val explicitName get() = this@map.explicitName
        override fun startMatching(continueWith: MatchingContinuation<Mapped>): OngoingMatch = this@map.startMatching(MappingContinuation(continueWith, mapper))
    }
}

private class MappingContinuation<Base : Any, Mapped : Any>(
    val mappedContinuation: MatchingContinuation<Mapped>,
    val mapper: (MatchingResult<Base>) -> MatchingResult<Mapped>,
) : MatchingContinuation<Base> {
    override fun resume(result: MatchingResult<Base>): OngoingMatch {
        return mappedContinuation.resume(mapper(result))
    }
}

/**
 * Like map, but requires the mapper to act on the results only
 */
fun <B : Any, A : Any> Rule<B>.mapResult(mapper: (B) -> A): Rule<A> = map { it ->
    MatchingResult(
        item = it.item?.let(mapper),
        reportings = it.reportings,
    )
}

/**
 * Flattens all response objects into a single [TransactionalSequence]. Collections and sub-results will be traversed.
 * Also, collects all the reportings into one flat structure
 */
fun Rule<*>.flatten(): Rule<TransactionalSequence<Any, Position>> {
    return map { base ->
        if (base.item == null) {
            @Suppress("UNCHECKED_CAST")
            return@map base as MatchingResult<TransactionalSequence<Any, Position>>
        }

        val itemBucket: MutableList<Any> = LinkedList()
        val reportingsBucket: MutableSet<ParsingMismatchReporting> = HashSet()

        fun collectFrom(result: MatchingResult<*>) {
            reportingsBucket.addAll(result.reportings)
            when (result.item) {
                is TransactionalSequence<*, *> -> itemBucket.addAll(result.item.remainingToList().filterNotNull())
                is SequenceRule.MatchedSequence -> result.item.subResults.forEach(::collectFrom)
                is RepeatingRule.RepeatedMatch<*> -> result.item.matches.forEach(::collectFrom)
                is EndOfInputToken -> {}
                Unit -> {}
                else -> result.item?.let(itemBucket::add)
            }
        }

        collectFrom(base)

        return@map MatchingResult(
            item = SimpleTransactionalSequence(itemBucket),
            reportings = reportingsBucket,
        )
    }
}

fun <T> Rule<TransactionalSequence<T, Position>>.trimWhitespaceTokens(front: Boolean = true, back: Boolean = true): Rule<TransactionalSequence<T, Position>> {

    val isWhitespace: (T) -> Boolean = { compiler.parser.isNewline(it as Any) }

    return this.mapResult { tokens ->
        val tokenList = tokens.remainingToList()

        if (front) tokenList.dropWhile(isWhitespace)
        if (back) tokenList.dropLastWhile(isWhitespace)

        return@mapResult SimpleTransactionalSequence(tokenList)
    }
}

/**
 * Operates on all [MatchingResult]s emitted by the receiver rule.
 * Runs all [Reporting]s of the receiver that have a level of [Reporting.Level.ERROR] or higher and are matched by the
 * given `predicate` through the `enhance` function; the [Reporting]s passed into `enhance` are not returned.
 */
fun <T : Any> Rule<T>.enhanceErrors(predicate: (ParsingMismatchReporting) -> Boolean, enhance: (ParsingMismatchReporting) -> ParsingMismatchReporting): Rule<T> {

    val enhancerMapper: (ParsingMismatchReporting) -> ParsingMismatchReporting = { reporting ->
        if (reporting.level >= Reporting.Level.ERROR && predicate(reporting))
            enhance(reporting)
        else reporting
    }

    return map { baseResult ->
        if (baseResult.reportings.isEmpty()) {
            return@map baseResult
        }

        return@map MatchingResult(
            item = baseResult.item,
            reportings = baseResult.reportings.map(enhancerMapper).toSet()
        )
    }
}