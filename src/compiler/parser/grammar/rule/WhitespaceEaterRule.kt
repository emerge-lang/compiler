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

import compiler.parser.TokenSequence
import compiler.parser.isWhitespace

/**
 * Skips whitespace in the input stream
 */
class WhitespaceEaterRule : Rule<Unit> {
    override val explicitName = null
    override val descriptionOfAMatchingThing = "optional whitespace"

    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<Unit> {
        while (input.hasNext()) {
            input.mark()
            val token = input.next()!!
            if (!isWhitespace(token)) {
                input.rollback()
                break
            }

            input.commit()
        }

        return RuleMatchingResult(
            true,
            Unit,
            emptySet()
        )
    }

    override val minimalMatchingSequence = sequenceOf(emptySequence<ExpectedToken>())

    companion object {
        val INSTANCE: WhitespaceEaterRule = WhitespaceEaterRule()
    }
}