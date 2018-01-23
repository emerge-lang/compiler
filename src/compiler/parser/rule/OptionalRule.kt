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

package compiler.parser.rule

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence

class OptionalRule<T>(
        val subRule: Rule<T>
): Rule<T?>
{
    override val descriptionOfAMatchingThing: String
        get() = "optional " + subRule.descriptionOfAMatchingThing

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<T?> {
        val subResult = subRule.tryMatch(input)

        if (subResult.item == null) {
            if (subResult.certainty >= ResultCertainty.MATCHED) {
                return RuleMatchingResultImpl(
                    ResultCertainty.NOT_RECOGNIZED,
                    subResult.item,
                    subResult.reportings
                )
            }
            else {
                return RuleMatchingResultImpl(
                    ResultCertainty.NOT_RECOGNIZED,
                    null,
                    emptySet()
                )
            }
        }

        return subResult
    }
}
