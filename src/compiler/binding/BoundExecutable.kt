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
import compiler.ast.expression.Expression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.reportings.Reporting

interface BoundExecutable<out ASTType> {
    /**
     * The context this expression has been bound to.
     */
    val context: CTContext

    /**
     * The [Expression] that was bound to [context].
     */
    val declaration: ASTType

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
     * Communicates changes the [Executable] applies any changes to its enclosing scope (e.g. a variable declaration declares a new
     * variable)
     * @return A [CTContext] derived from the given one, with all the necessary changes applied.
     */
    fun modified(context: CTContext): CTContext = context

    /**
     * Must be invoked before [semanticAnalysisPhase3].
     *
     * Sets the type that [BoundReturnStatement] within this executable are expected to return. When this method has
     * been invoked the types evaluated for all [BoundReturnStatement]s within this executable must be assignable to that
     * given type; otherwise an appropriate reporting as to returned from [semanticAnalysisPhase3].
     */
    fun enforceReturnType(type: BaseTypeReference) {}

    /**
     * This method is in place to verify explicit mentions of types in expressions. At the current stage,
     * this affects no expression. In the future, there will be expressions that can (or event must) contain
     * such explicit mentions:
     * * casts
     * * explicit generics
     */
    fun semanticAnalysisPhase1(): Collection<Reporting> = emptySet()

    /**
     * This method does currently not affect any expression. In the future, these expressions will make
     * good use of this method:
     * * constructor invocations
     * * method references (both static ones and such with a context)
     */
    fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()

    /**
     * Here is where actual semantics are validated.
     */
    fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()

    /**
     * Use to find violations of purity.
     * @param boundary The boundary. The boundary context must be in the [CTContext.hierarchy] of `this`' context.
     * @return All the nested [BoundExecutable]s (or `this` if there are no nested ones) that read state that belongs
     *         to context outside of the given boundary.
     */
    fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> = emptySet() // TODO remove default impl

    /**
     * Use to find violations of readonlyness and/or purity.
     * @param boundary The boundary. The boundary context must be in the [CTContext.hierarchy] of `this`' context.
     * @return All the nested [BoundExecutable]s (or `this` if there are no nested ones) that write state that belongs
     *         to context outside of the given boundary.
     */
    fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> = emptySet() // TODO remove default impl
}