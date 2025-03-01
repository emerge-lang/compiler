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
import compiler.lexer.Token
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.RepeatingRule
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.SequenceRule
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
        override fun match(tokens: Array<Token>, atIndex: Int): Sequence<MatchingResult<Mapped>> {
            return this@map.match(tokens, atIndex).map(mapper)
        }
    }
}
/**
 * Like map, but requires the mapper to act on the results only
 */
fun <B : Any, A : Any> Rule<B>.mapResult(mapper: (B) -> A): Rule<A> = map {
    when (it) {
        is MatchingResult.Success -> MatchingResult.Success(mapper(it.item), it.continueAtIndex)
        is MatchingResult.Error -> it
    }
}

/**
 * Flattens all response objects into a single [TransactionalSequence]. Collections and sub-results will be traversed.
 * Also, collects all the [Diagnostic]s into one flat structure
 */
fun Rule<*>.flatten(): Rule<TransactionalSequence<Any, Position>> {
    return mapResult { base ->
        val itemBucket: MutableList<Any> = LinkedList()

        fun collectFrom(result: Any) {
            when (result) {
                is TransactionalSequence<*, *> -> itemBucket.addAll(result.remainingToList().filterNotNull())
                is SequenceRule.MatchedSequence -> result.subResults.forEach(::collectFrom)
                is RepeatingRule.RepeatedMatch<*> -> result.matches.forEach(::collectFrom)
                is EndOfInputToken -> {}
                Unit -> {}
                is MatchingResult.Success<*> -> collectFrom(result.item)
                else -> itemBucket.add(result)
            }
        }

        collectFrom(base)

        SimpleTransactionalSequence(itemBucket)
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