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

import compiler.ast.expression.UnaryExpression
import compiler.binding.BoundStatement
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.type.BoundTypeReference
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import compiler.reportings.UnresolvableFunctionOverloadReporting

class BoundUnaryExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: UnaryExpression,
    private val hiddenInvocation: BoundInvocationExpression,
) : BoundExpression<UnaryExpression> {

    override var type: BoundTypeReference? = null
        private set

    override val throwBehavior get() = hiddenInvocation.throwBehavior
    override val returnBehavior get() = hiddenInvocation.returnBehavior

    override fun semanticAnalysisPhase1() = hiddenInvocation.semanticAnalysisPhase1()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        hiddenInvocation.semanticAnalysisPhase2()
            .map { hiddenReporting ->
                if (hiddenReporting !is UnresolvableFunctionOverloadReporting) {
                    return@map hiddenReporting
                }

                Reporting.operatorNotDeclared(
                    "Unary operator ${declaration.operatorToken.operator} (function ${hiddenInvocation.functionNameToken.value}) not declared for type ${hiddenReporting.receiverType ?: "<unknown>"}",
                    declaration,
                )
            }
            .let(reportings::addAll)

        hiddenInvocation.functionToInvoke?.let { operatorFunction ->
            if (!operatorFunction.attributes.isDeclaredOperator) {
                reportings.add(
                    Reporting.functionIsMissingAttribute(
                        operatorFunction,
                        this.declaration,
                        "operator",
                    )
                )
            }
        }

        return reportings
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        hiddenInvocation.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> = hiddenInvocation.semanticAnalysisPhase3()

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return hiddenInvocation.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        return hiddenInvocation.findWritesBeyond(boundary)
    }

    override val isEvaluationResultReferenceCounted get() = hiddenInvocation.isEvaluationResultReferenceCounted
    override val isCompileTimeConstant get() = hiddenInvocation.isCompileTimeConstant

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do here: the only way to use this information would be the return type of the operator function
        // overload resolution based on return type is not a thing in Emerge
    }

    override fun toBackendIrStatement() = hiddenInvocation.toBackendIrStatement()
    override fun toBackendIrExpression() = hiddenInvocation.toBackendIrExpression()
}

