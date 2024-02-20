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
import compiler.binding.expression.BoundExpression
import compiler.binding.type.BoundTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

interface BoundExecutable<out AstNode : Executable> : BoundElement<AstNode> {
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
    val mayReturn: Boolean
        get() = false

    /**
     * Whether this executable is guaranteed to throw an exception.
     *
     * Must not be `null` after semantic analysis is complete.
     */
    val isGuaranteedToThrow: Boolean?

    /**
     * When implicitly evaluating the result of this executable, this type is returned. Available after
     * [semanticAnalysisPhase2]. Need not be set unless [BoundExecutable.requireImplicitEvaluationTo] is called.
     */
    val implicitEvaluationResultType: BoundTypeReference?

    /**
     * A context derived from the one bound to ([context]), containing all the changes the [Executable] applies
     * to its enclosing scope (e.g. a variable declaration add a new variable)
     */
    val modifiedContext: CTContext
        get() = context

    /**
     * Must be invoked before [semanticAnalysisPhase2]
     *
     * If invoked, the last statement in this executable must be an expression. If that's not the case, an appropriate
     * reporting will be returned from [semanticAnalysisPhase2]. This very last expression will use [type] for type
     * inference.
     * @see BoundExpression.setExpectedEvaluationResultType
     */
    fun requireImplicitEvaluationTo(type: BoundTypeReference)

    /**
     * Must be invoked before [semanticAnalysisPhase3].
     *
     * Sets the type that [BoundReturnStatement]s within this executable are expected to return. When this method has
     * been invoked the types evaluated for all [BoundReturnStatement]s within this executable must be assignable to that
     * given type; otherwise an appropriate reporting as to returned from [semanticAnalysisPhase3].
     */
    fun setExpectedReturnType(type: BoundTypeReference) {}

    /**
     * Use to find violations of purity.
     * @param boundary The boundary. The boundary context must be in the [CTContext.hierarchy] of `this`' context.
     * @return All the nested [BoundExecutable]s (or `this` if there are no nested ones) that read state that belongs
     *         to context outside the given boundary.
     */
    fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> = emptySet() // TODO remove default impl

    /**
     * Use to find violations of readonlyness and/or purity.
     * @param boundary The boundary. The boundary context must be in the [CTContext.hierarchy] of `this`' context.
     * @return All the nested [BoundExecutable]s (or `this` if there are no nested ones) that write state that belongs
     *         to context outside the given boundary.
     */
    fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> = emptySet() // TODO remove default impl

    /**
     * TODO: most classes have a backing lazy field. The method is nonsense, refactor to a val
     */
    fun toBackendIr(): IrExecutable
}