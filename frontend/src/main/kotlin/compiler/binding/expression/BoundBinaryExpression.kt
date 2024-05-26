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

import compiler.ast.Expression
import compiler.ast.expression.BinaryExpression
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.reportings.FunctionMissingModifierReporting
import compiler.reportings.Reporting
import compiler.reportings.UnresolvableFunctionOverloadReporting

class BoundBinaryExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: BinaryExpression,
    val hiddenInvocation: BoundInvocationExpression,
) : BoundExpression<Expression> by hiddenInvocation {
    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        if (type is RootResolvedTypeReference && type.baseType.isCoreScalar) {
            hiddenInvocation.receiverExpression!!.setExpectedEvaluationResultType(type)
            hiddenInvocation.valueArguments[0].setExpectedEvaluationResultType(type)
        }

        hiddenInvocation.setExpectedEvaluationResultType(type)
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        hiddenInvocation.semanticAnalysisPhase2()
            .map { hiddenReporting ->
                if (hiddenReporting !is UnresolvableFunctionOverloadReporting) {
                    return@map hiddenReporting
                }

                Reporting.operatorNotDeclared(
                    "Binary operator ${declaration.operator.name} (function ${hiddenInvocation.functionNameToken.value}) not declared for type ${hiddenReporting.receiverType ?: "<unknown>"}",
                    declaration,
                )
            }
            .let(reportings::addAll)

        FunctionMissingModifierReporting.requireOperatorModifier(
            hiddenInvocation,
            this,
            reportings,
        )

        return reportings
    }
}