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

package compiler.binding.expression

import compiler.binding.BoundExecutable
import compiler.binding.type.BoundTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

interface BoundExpression<out ASTType> : BoundExecutable<ASTType> {
    /**
     * The type of this expression when evaluated. If the type could not be determined due to semantic errors,
     * this might be a guess or null.
     */
    val type: BoundTypeReference?

    /**
     * To be called before [BoundExecutable.semanticAnalysisPhase2]. Information from the desired type
     * is used to disambiguate and simplify semantic analysis in this expression. Example use cases:
     * * a newly constructed object can be assigned to both a `mutable` and `immutable` reference, which isn't
     *   possible in any other case. This method allows the constructor-invocation-expression to tack the correct
     *   mutability onto the return type
     * * lambda functions need to know the type of their parameters to be validated. That information comes from the
     *   called function declaration, through this method.
     */
    fun setExpectedEvaluationResultType(type: BoundTypeReference)

    /**
     * Must be called during after [BoundExecutable.semanticAnalysisPhase1] and before [BoundExecutable.semanticAnalysisPhase2]
     * by the enclosing code running this expression. The intended purposes are:
     * * in the frontend
     *   * detect whether a [BoundIdentifierExpression] is used in read context ([markEvaluationResultUsed] was called)
     *     or in write context ([markEvaluationResultUsed] was not called). Ultimately drives whether initialization of a
     *     referred variable is required.
     * * in the backend:
     *   * detect whether a function invocation returning `Unit` can be left to be optimized to `void` or
     *     whether an artificial reference to `Unit` needs to be generated.
     */
    fun markEvaluationResultUsed() {}

    override fun toBackendIr(): IrExpression {
        TODO("for ${this::class.simpleName}")
    }
}