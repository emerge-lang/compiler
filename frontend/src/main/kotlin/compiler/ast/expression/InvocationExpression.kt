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

package compiler.ast.expression

import compiler.InternalCompilerError
import compiler.ast.Expression
import compiler.ast.Expression.Companion.chain
import compiler.ast.type.AstTypeArgument
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.BoundInvocationExpression
import compiler.lexer.Span

class InvocationExpression(
    /**
     * The target of the invocation. e.g.:
     * * `doStuff()` => `IdentifierExpression(doStuff)`
     * * `obj.doStuff()` => `MemberAccessExpression(obj, doStuff)`
     */
    val targetExpression: Expression,
    val typeArguments: List<AstTypeArgument>?,
    val argumentExpressions: List<Expression>,
    override val span: Span,
) :Expression {
    override fun bindTo(context: ExecutionScopedCTContext): BoundInvocationExpression = bindTo(context, null, BoundInvocationExpression.DisambiguationBehavior.AllParametersDisambiguate)

    fun bindTo(
        context: ExecutionScopedCTContext,
        candidateFilter: BoundInvocationExpression.CandidateFilter?,
        disambiguationBehavior: BoundInvocationExpression.DisambiguationBehavior = BoundInvocationExpression.DisambiguationBehavior.AllParametersDisambiguate,
    ): BoundInvocationExpression {
        val boundReceiver = (targetExpression as? MemberAccessExpression)?.valueExpression?.bindTo(context)
        val contextAfterReceiver = boundReceiver?.modifiedContext ?: context
        val boundArguments = argumentExpressions.chain(contextAfterReceiver).toList()
        val contextAfterArguments = boundArguments.lastOrNull()?.modifiedContext ?: contextAfterReceiver
        val functionNameToken = when (targetExpression) {
            is MemberAccessExpression -> targetExpression.memberName
            is IdentifierExpression -> targetExpression.identifier
            else -> throw InternalCompilerError("What the heck is going on?? The parser should never have allowed this!")
        }

        return BoundInvocationExpression(
                contextAfterArguments,
            context,
            this,
            boundReceiver,
            functionNameToken,
            boundArguments,
            candidateFilter,
            disambiguationBehavior,
        )
    }
}