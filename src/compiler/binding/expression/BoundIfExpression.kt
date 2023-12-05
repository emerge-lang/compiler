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

import compiler.ast.expression.Expression
import compiler.ast.expression.IfExpression
import compiler.binding.BoundExecutable
import compiler.binding.context.CTContext
import compiler.binding.type.ResolvedTypeReference
import compiler.binding.type.BuiltinBoolean
import compiler.binding.type.Unit
import compiler.binding.type.isAssignableTo
import compiler.nullableAnd
import compiler.reportings.Reporting

class BoundIfExpression(
    override val context: CTContext,
    override val declaration: IfExpression,
    val condition: BoundExpression<Expression<*>>,
    val thenCode: BoundExecutable<*>,
    val elseCode: BoundExecutable<*>?
) : BoundExpression<IfExpression>, BoundExecutable<IfExpression> {
    override val isGuaranteedToThrow: Boolean
        get() = thenCode.isGuaranteedToThrow nullableAnd (elseCode?.isGuaranteedToThrow ?: false)

    override val isGuaranteedToReturn: Boolean
        get() {
            if (elseCode == null) {
                return false
            }
            else {
                return thenCode.isGuaranteedToReturn nullableAnd elseCode.isGuaranteedToReturn
            }
        }

    override var type: ResolvedTypeReference? = null
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        var reportings = condition.semanticAnalysisPhase1() + thenCode.semanticAnalysisPhase1()

        val elseCodeReportings = elseCode?.semanticAnalysisPhase1()
        if (elseCodeReportings != null) {
            reportings = reportings + elseCodeReportings
        }

        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        var reportings = condition.semanticAnalysisPhase2() + thenCode.semanticAnalysisPhase2()

        val elseCodeReportings = elseCode?.semanticAnalysisPhase2()
        if (elseCodeReportings != null) {
            reportings = reportings + elseCodeReportings
        }

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        reportings.addAll(condition.semanticAnalysisPhase3())
        reportings.addAll(thenCode.semanticAnalysisPhase3())

        if (elseCode != null) {
            reportings.addAll(elseCode.semanticAnalysisPhase3())
        }

        if (condition.type != null) {
            val conditionType = condition.type!!
            if (!conditionType.isAssignableTo(BuiltinBoolean.baseReference(context))) {
                reportings.add(Reporting.conditionIsNotBoolean(condition, condition.declaration.sourceLocation))
            }
        }

        val thenType = if (thenCode is BoundExpression<*>) thenCode.type else Unit.baseReference(context)
        val elseType = if (elseCode is BoundExpression<*>) elseCode.type else Unit.baseReference(context)

        if (thenType != null && elseType != null) {
            type = thenType.closestCommonSupertypeWith(elseType)
        }

        condition.findWritesBeyond(context).forEach { mutationInCondition ->
            if (mutationInCondition is BoundAssignmentExpression) {
                reportings.add(Reporting.assignmentInCondition(mutationInCondition))
            } else {
                reportings.add(Reporting.mutationInCondition(mutationInCondition))
            }
        }

        return reportings
    }

    override fun setExpectedReturnType(type: ResolvedTypeReference) {
        thenCode.setExpectedReturnType(type)
        elseCode?.setExpectedReturnType(type)
    }
}