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

import compiler.parser.rule.RuleMatchingResult

/**
 * To be thrown **ONLY** from functions defined in [GrammarReceiver] and [BaseMatchingGrammarReceiver].
 * Is "abused" to change the control flow from within a [Grammar] when it does not match the input. This may get
 * replaced by some low level coroutine magic later on.
 */
open class MatchingAbortedException(val result: RuleMatchingResult<*>, message: String = "Matching aborted because a sub-rule did not match; see the reportings variable") : Exception(message)