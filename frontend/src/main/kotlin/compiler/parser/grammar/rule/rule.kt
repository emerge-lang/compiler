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

package compiler.parser.grammar.rule

import compiler.lexer.EndOfInputToken
import compiler.lexer.Token
import compiler.parser.TokenSequence

interface Rule<out Item : Any> {
    val explicitName: String?

    fun startMatching(continueWith: MatchingContinuation<Item>): OngoingMatch

    fun match(tokens: TokenSequence): MatchingResult<Item> {
        require(tokens.hasNext()) { "Cannot match an empty token sequence" }
        val completion = FirstMatchCompletion<Item>()
        val ongoing = startMatching(completion)
        var previousAccepted = true
        lateinit var previous: Token
        while (previousAccepted && tokens.hasNext()) {
            previous = tokens.next()!!
            previousAccepted = ongoing.step(previous)
        }

        if (previousAccepted) {
            val eoiLocation = previous.span.copy(
                fromLineNumber = previous.span.toLineNumber,
                fromColumnNumber = previous.span.toColumnNumber + 1u,
                toLineNumber = previous.span.toLineNumber,
                toColumnNumber = previous.span.toColumnNumber + 1u,
            )
            ongoing.step(EndOfInputToken(eoiLocation))
        }

        return completion.result
    }
}

interface MatchingContinuation<in Item : Any> {
    fun resume(result: MatchingResult<Item>): OngoingMatch

}

/**
 * The state machine of matching a rule against a stream of tokens. Consumes one token at a time.
 */
interface OngoingMatch {
    fun step(token: Token): Boolean

    object Completed : OngoingMatch {
        override fun step(token: Token) = false
    }
}