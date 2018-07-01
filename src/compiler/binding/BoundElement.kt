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
import compiler.reportings.Reporting

/**
 * Anything that resulted from AST and that can have compile time checks.
 */
interface BoundElement<out ASTType> {
    /**
     * The context this expression has been bound to.
     */
    val context: CTContext

    /**
     * The [Expression] that was bound to [context].
     */
    val declaration: ASTType

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