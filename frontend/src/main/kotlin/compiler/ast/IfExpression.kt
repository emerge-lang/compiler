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

package compiler.ast

import compiler.binding.BoundCondition
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.expression.BoundIfExpression
import compiler.lexer.Span

class IfExpression (
    override val span: Span,
    val condition: Expression,
    val thenCode: Executable,
    val elseCode: Executable?
) : Expression {
    override fun bindTo(context: ExecutionScopedCTContext): BoundIfExpression {
        val contextBeforeCondition: ExecutionScopedCTContext = MutableExecutionScopedCTContext.deriveFrom(context)
        val boundCondition = BoundCondition(condition.bindTo(contextBeforeCondition))

        val thenCodeAsChunk: AstCodeChunk = if (thenCode is AstCodeChunk) thenCode else AstCodeChunk(listOf(thenCode as Statement))
        val elseCodeAsChunk: AstCodeChunk? = if (elseCode == null) null else if (elseCode is AstCodeChunk) elseCode else AstCodeChunk(listOf(elseCode as Statement))

        return BoundIfExpression(
            contextBeforeCondition,
            this,
            boundCondition,
            thenCodeAsChunk.bindTo(boundCondition.modifiedContext),
            elseCodeAsChunk?.bindTo(contextBeforeCondition),
        )
    }
}