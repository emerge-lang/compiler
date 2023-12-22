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
import compiler.binding.type.ResolvedTypeReference

interface BoundExpression<out ASTType> : BoundExecutable<ASTType> {
    /**
     * The type of this expression when evaluated If the type could not be determined due to semantic errors,
     * this might be a close guess or null.
     */
    val type: ResolvedTypeReference?

    /**
     * To be called before [BoundExecutable.semanticAnalysisPhase2]. Information from the desired type
     * is used to disambiguate and simplify semantic analysis in this expression. Example use cases:
     * * a newly constructed object can be assigned to both a `mutable` and `immutable` reference, which isn't
     *   possible in any other case. This method allows the constructor-invocation-expression to tack the correct
     *   mutability onto the return type
     * * lambda functions need to know the type of their parameters to be validated. That information comes from the
     *   called function declaration, through this method.
     */
    fun setExpectedEvaluationResultType(type: ResolvedTypeReference)
}