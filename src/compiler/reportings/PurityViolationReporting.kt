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

import compiler.ast.Executable
import compiler.ast.type.FunctionModifier
import compiler.binding.expression.BoundAssignmentExpression
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundInvocationExpression

abstract class PurityViolationReporting protected constructor(val violation: BoundExecutable<Executable<*>>, function: BoundFunction, message: String)
    : Reporting(Level.ERROR, message, violation.declaration.sourceLocation)

data class ReadInPureContextReporting internal constructor(val readingExpression: BoundIdentifierExpression, val function: BoundFunction) : PurityViolationReporting(
    readingExpression,
    function,
    "pure function ${function.name} cannot read ${readingExpression.identifier} (is not within the pure boundary)"
)

data class ImpureInvocationInPureContextReporting internal constructor(val invcExpr: BoundInvocationExpression, val function: BoundFunction) : PurityViolationReporting(
    invcExpr,
    function,
    "pure function ${function.name} cannot invoke impure function ${invcExpr.dispatchedFunction!!.name}"
)

data class ModifyingInvocationInReadonlyContextReporting internal constructor(val invcExpr: BoundInvocationExpression, val function: BoundFunction) : PurityViolationReporting(
    invcExpr,
    function,
    "readonly function ${function.name} cannot invoke modifying function ${invcExpr.dispatchedFunction!!.name}"
)

data class StateModificationOutsideOfPurityBoundaryReporting internal constructor(val assignment: BoundAssignmentExpression, val function: BoundFunction) : PurityViolationReporting(
    assignment,
    function,
    {
        val functionType = if (FunctionModifier.PURE in function.modifiers) FunctionModifier.PURE else FunctionModifier.READONLY
        val functionTypeAsString = functionType.name[0].toUpperCase() + functionType.name.substring(1).toLowerCase()
        val boundaryType = if (functionType == FunctionModifier.PURE) "purity" else "readonlyness"

        "$functionTypeAsString function ${function.name} cannot assign state outside of its $boundaryType boundary"
    }()
)