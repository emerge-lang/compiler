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
import compiler.reportings.Reporting

/**
 * Matches the end of the given token sequence
 * TODO: can this stay a singleton in light of [ExpectedToken.isCloneOf] asking for a distinction between every mention of this rule?
 */
class EOIRule private constructor() : Rule<Unit> {
    private val marksEndOfAmbiguityInContexts = HashSet<Any>()
    override val explicitName = null
    override val descriptionOfAMatchingThing = "end of input"
    override fun toString(): String = descriptionOfAMatchingThing
    override fun tryMatch(context: Any, input: TokenSequence): RuleMatchingResult<Unit> {
        if (input.hasNext()) {
            return RuleMatchingResult(
                isAmbiguous = true,
                marksEndOfAmbiguity = false,
                null,
                setOf(Reporting.mismatch(descriptionOfAMatchingThing, input.peek()!!))
            )
        }

        return RuleMatchingResult(
            isAmbiguous = false,
            marksEndOfAmbiguity = context in marksEndOfAmbiguityInContexts,
            item = Unit,
            reportings = emptySet()
        )
    }

    private val expectedToken: ExpectedToken = object : ExpectedToken {
        override fun markAsRemovingAmbiguity(inContext: Any) {
            marksEndOfAmbiguityInContexts.add(inContext)
        }

        override fun toString() = "<end of input>"

        override fun couldMatchSameTokenAs(other: ExpectedToken) = other === this
    }

    override val minimalMatchingSequence = sequenceOf(sequenceOf(expectedToken))

    companion object {
        val INSTANCE = EOIRule()
    }
}
