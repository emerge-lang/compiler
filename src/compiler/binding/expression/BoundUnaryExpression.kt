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

import compiler.ast.Executable
import compiler.ast.expression.UnaryExpression
import compiler.ast.type.FunctionModifier
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext
import compiler.binding.filterAndSortByMatchForInvocationTypes
import compiler.binding.type.BaseTypeReference
import compiler.lexer.Operator
import compiler.reportings.Reporting

class BoundUnaryExpression(
    override val context: CTContext,
    override val declaration: UnaryExpression,
    val original: BoundExpression<*>
) : BoundExpression<UnaryExpression> {

    override var type: BaseTypeReference? = null
        private set

    val operator = declaration.operator

    var operatorFunction: BoundFunction? = null
        private set

    override val isGuaranteedToThrow = original.isGuaranteedToThrow // the unary operator THEORETICALLY can always throw; not in this language, though

    override fun semanticAnalysisPhase1() = original.semanticAnalysisPhase1()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(original.semanticAnalysisPhase2())

        if (original.type == null) {
            // failed to determine base type - cannot infer unary operator
            return reportings
        }

        val valueType = original.type!!

        // determine operator function
        val opFunName = operatorFunctionName(operator)

        // functions with receiver
        val receiverOperatorFuns =
            context.resolveFunction(opFunName)
                .filterAndSortByMatchForInvocationTypes(valueType, emptyList())
                .sortedByDescending { FunctionModifier.OPERATOR in it.declaration.modifiers }

        operatorFunction = receiverOperatorFuns.firstOrNull()

        if (operatorFunction != null) {
            if (FunctionModifier.OPERATOR !in operatorFunction!!.modifiers) {
                reportings.add(Reporting.functionIsMissingModifier(operatorFunction!!, this.declaration, FunctionModifier.OPERATOR))
            } else {
                reportings.add(
                    Reporting.operatorNotDeclared(
                        "Unary operator $operator (function $opFunName) not declared for type $valueType",
                        declaration
                    )
                )
            }
        }

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return original.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return original.findWritesBeyond(boundary)

        // unary operators are readonly by definition; the check for that happens inside the corresponding BoundFunction
    }
}

private fun operatorFunctionName(op: Operator): String = when(op) {
    else -> "unary" + op.name[0].uppercase() + op.name.substring(1).lowercase()
}