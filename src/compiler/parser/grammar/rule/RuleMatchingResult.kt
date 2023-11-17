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

import compiler.parser.grammar.dsl.eitherOf
import compiler.reportings.Reporting

/**
 * When a [Rule] is matched against an input it returns an [RuleMatchingResult] that describes
 * the outcome of the matching process.
 */
class RuleMatchingResult<out ItemType>(
    /**
     * If false, the result is unambiguous in the original context ([Rule.tryMatch]), especially
     * relevant on [eitherOf] rules.
     */
    val isAmbiguous: Boolean,

    /**
     * The [item] may only be null if the given input did not contain enough information to construct a meaningful item.
     */
    val item: ItemType?,

    /**
     * Along with the [item] of the match, an [RuleMatchingResult] can provide the caller with additional reportings
     * about the matched input. If the input did not match the expectations of the [Rule] that could be details on what
     * expectations were not met.
     */
    val reportings: Collection<Reporting>,
) {
    /** Whether one of the reportings is of level [Reporting.Level.ERROR] or higher */
    val hasErrors: Boolean
        get() = this.reportings.find { it.level >= Reporting.Level.ERROR } != null
}