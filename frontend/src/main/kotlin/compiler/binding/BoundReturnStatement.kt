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
import compiler.ast.ReturnStatement
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Reporting
import compiler.reportings.ReturnTypeMismatchReporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrReturnStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrStatement

class BoundReturnStatement(
    override val context: CTContext,
    override val declaration: ReturnStatement
) : BoundExecutable<ReturnStatement> {

    private var expectedReturnType: BoundTypeReference? = null

    val expression = declaration.expression.bindTo(context)

    var returnType: BoundTypeReference? = null
        private set

    override val isGuaranteedToReturn = true // this is the core LoC that makes the property work big-scale
    override val mayReturn = true            // this is the core LoC that makes the property work big-scale

    override val isGuaranteedToThrow = expression.isGuaranteedToThrow

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return expression.semanticAnalysisPhase1()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return expression.semanticAnalysisPhase2()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings += expression.semanticAnalysisPhase3()

        val expectedReturnType = this.expectedReturnType
            ?: return reportings + Reporting.consecutive("Cannot check return value type because the expected return type is not known", declaration.sourceLocation)
        val expressionType = expression.type

        if (expressionType != null) {
            expressionType.evaluateAssignabilityTo(expectedReturnType, declaration.sourceLocation)
                ?.let {
                    reportings.add(ReturnTypeMismatchReporting(it))
                }
        }

        return reportings
    }

    override fun setExpectedReturnType(type: BoundTypeReference) {
        expectedReturnType = type
        expression.setExpectedEvaluationResultType(type)
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return this.expression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return this.expression.findWritesBeyond(boundary)
    }

    override fun toBackendIr(): IrStatement {
        return IrReturnStatementImpl(this.expression.toBackendIr())
    }
}

private class IrReturnStatementImpl(override val value: IrExpression) : IrReturnStatement