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

package compiler.reportings

import compiler.ast.type.FunctionModifier
import compiler.binding.BoundAssignmentStatement
import compiler.binding.BoundFunction
import compiler.binding.BoundStatement
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundInvocationExpression

abstract class PurityViolationReporting protected constructor(
    val violation: BoundStatement<*>,
    message: String
)
    : Reporting(Level.ERROR, message, violation.declaration.sourceLocation)

data class ReadInPureContextReporting internal constructor(val readingExpression: BoundIdentifierExpression, val function: BoundFunction) : PurityViolationReporting(
    readingExpression,
    "pure function ${function.name} cannot read ${readingExpression.identifier} (is not within the pure boundary)"
) {
    override fun toString() = super.toString()
}

data class ImpureInvocationInPureContextReporting internal constructor(val invcExpr: BoundInvocationExpression, val function: BoundFunction) : PurityViolationReporting(
    invcExpr,
    "pure function ${function.name} cannot invoke impure function ${invcExpr.dispatchedFunction!!.name}"
) {
    override fun toString() = super.toString()
}

data class ModifyingInvocationInReadonlyContextReporting internal constructor(val invcExpr: BoundInvocationExpression, val function: BoundFunction) : PurityViolationReporting(
    invcExpr,
    "readonly function ${function.name} cannot invoke modifying function ${invcExpr.dispatchedFunction!!.name}"
) {
    override fun toString() = super.toString()
}

data class StateModificationOutsideOfPurityBoundaryReporting internal constructor(val assignment: BoundAssignmentStatement, val function: BoundFunction) : PurityViolationReporting(
    assignment,
    {
        val functionType = if (FunctionModifier.Pure in function.modifiers) FunctionModifier.Pure else FunctionModifier.Readonly
        val functionTypeAsString = functionType::class.simpleName
        val boundaryType = if (functionType == FunctionModifier.Pure) "purity" else "readonlyness"

        "$functionTypeAsString function ${function.name} cannot assign state outside of its $boundaryType boundary"
    }()
) {
    override fun toString() = super.toString()
}