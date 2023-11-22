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

interface Rule<T> {
    val descriptionOfAMatchingThing: String
    val explicitName: String?

    /**
     * @param context internal, crucial for ambiguity resolution. Unless you know **precisely** what to pass for this,
     * pass [MatchingContext.None], This doesn't have a default value to make you actively consider this, as missing it
     * out accidentally will produce ugly error messages on invalid grammar.
     */
    fun match(context: MatchingContext, input: TokenSequence): MatchingResult<T>

    /**
     * @return outer iterator: for each possible alternative in this rule (resolves [EitherOfRule] multitude of options):
     * an inner iterator of example tokens that describe the "prototype" of the ideal match to
     * this [Rule].
     * If this rule can produce a valid match without consuming a single token from the input, this method must return
     * `listOf(emptyList().iterator()).iterator()`.
     */
    val minimalMatchingSequence: Sequence<Sequence<ExpectedToken>>

    /**
     * **Internal to the rule engine.**
     *
     * On subsequent invocations to [match], the rule will not try to resolve ambiguity for the given context.
     * This makes sure rules do not re-evaluate ambiguity in a smaller context, possibly missing ambiguities only
     * present in their larger scope.
     */
    fun markAmbiguityResolved(inContext: MatchingContext)
}