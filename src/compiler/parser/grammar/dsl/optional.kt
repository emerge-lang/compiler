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

package compiler.parser.grammar.dsl

import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl

internal fun tryMatchOptional(rule: Rule<*>, input: TokenSequence): RuleMatchingResult<Any?> {
    val subResult = rule.tryMatch(input)

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
                Unit,
                emptySet()
            )
        }
    }

    return subResult
}