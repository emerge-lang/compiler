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

package compiler.ast.type

import compiler.lexer.IdentifierToken

/** Function modifiers */
sealed class FunctionModifier {
    open val impliesNoBody: Boolean = false

    /**
     * The function may only read from its enclosing context and only invoke other functions that are marked with
     * [Readonly] or that don't actually read from their enclosing context.
     */
    data object Readonly : FunctionModifier()

    /**
     * The function may not throw exceptions nor may it call other functions that throw exceptions.
     */
    data object Nothrow : FunctionModifier()

    /**
     * The function must not interact with its enclosing scope nor may it call other functions that do. That
     * assures that the function is deterministic and allows for aggressive optimization using CTFE.
     */
    data object Pure : FunctionModifier()

    /**
     * The function defines or overrides an operator.
     */
    data object Operator : FunctionModifier()

    /**
     * The body of the function is provided by the backend. Used for target-specific functions, usually
     * the smallest of building blocks (e.g. `Int.opPlus(Int)`)
     */
    data object Intrinsic : FunctionModifier() {
        override val impliesNoBody = true
    }

    data class External(val ffiName: IdentifierToken) : FunctionModifier() {
        override val impliesNoBody = true
    }
}