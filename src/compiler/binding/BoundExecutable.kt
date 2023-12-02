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

package compiler.binding

import compiler.ast.Executable
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

interface BoundExecutable<out ASTType> : BoundElement<Executable<*>> {
    /**
     * Whether this executable is guaranteed to return to the caller; with or without return value.
     *
     * Must not be `null` after semantic analysis is complete.
     */
    val isGuaranteedToReturn: Boolean?
        get() = false

    /**
     * Whether this executable may return to the caller; with or without return value.
     *
     * Must not be `null` after semantic analysis is complete.
     */
    val mayReturn: Boolean?
        get() = false

    /**
     * Whether this executable is guaranteed to throw an exception.
     *
     * Must not be `null` after semantic analysis is complete.
     */
    val isGuaranteedToThrow: Boolean?

    /**
     * A context derviced from the one bound to ([context]), containing all the changes the [Executable] applies
     * to its enclosing scope (e.g. a variable declaration add a new variable)
     */
    val modifiedContext: CTContext
        get() = context

    /**
     * Must be invoked before [semanticAnalysisPhase3].
     *
     * Sets the type that [BoundReturnStatement] within this executable are expected to return. When this method has
     * been invoked the types evaluated for all [BoundReturnStatement]s within this executable must be assignable to that
     * given type; otherwise an appropriate reporting as to returned from [semanticAnalysisPhase3].
     */
    fun setExpectedReturnType(type: BaseTypeReference) {}
}