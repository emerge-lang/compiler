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

/** Function modifiers */
enum class FunctionModifier {
    /**
     * The function may only read from its enclosing context and only invoke other functions that are marked with
     * [READONLY] or that don't actually read from their enclosing context.
     */
    READONLY,

    /**
     * The function may not throw exceptions nor may it call other functions that throw exceptions.
     */
    NOTHROW,

    /**
     * The function must not interact with its enclosing scope nor may it call other functions that do. That
     * assures that the function is deterministic and allows for aggressive optimization using CTFE.
     */
    PURE,

    /**
     * The function defines or overrides an operator.
     */
    OPERATOR,

    /**
     * The functions body is provided to the compiler by other means than source language code.
     *
     * For example, a lot of the builtin types use this modifier in their defining statements. At compile time the
     * compiler loads the function body appropriate for the compile target.
     */
    EXTERNAL
}