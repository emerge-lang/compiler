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

import compiler.binding.BoundAssignmentStatement
import compiler.binding.BoundStatement
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundInvocationExpression

abstract class PurityViolationReporting protected constructor(
    val violation: BoundStatement<*>,
    message: String
) : Reporting(Level.ERROR, message, violation.declaration.span) {
}

class ReadInPureContextReporting internal constructor(val readingExpression: BoundIdentifierExpression, val boundary: SideEffectBoundary) : PurityViolationReporting(
    readingExpression,
    "$boundary cannot read ${readingExpression.identifier} (is not within the purity-boundary)"
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ReadInPureContextReporting) return false

        if (readingExpression.declaration.span != other.readingExpression.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        return readingExpression.declaration.span.hashCode()
    }
}

class ImpureInvocationInPureContextReporting internal constructor(val invcExpr: BoundInvocationExpression, val boundary: SideEffectBoundary) : PurityViolationReporting(
    invcExpr,
    "$boundary cannot invoke impure function ${invcExpr.functionToInvoke!!.name}"
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ImpureInvocationInPureContextReporting) return false

        if (invcExpr.declaration.span != other.invcExpr.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        return invcExpr.declaration.span.hashCode()
    }
}

class ModifyingInvocationInReadonlyContextReporting internal constructor(val invcExpr: BoundInvocationExpression, val boundary: SideEffectBoundary) : PurityViolationReporting(
    invcExpr,
    "$boundary cannot invoke modifying function ${invcExpr.functionToInvoke!!.name}"
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ModifyingInvocationInReadonlyContextReporting) return false

        if (invcExpr.declaration.span != other.invcExpr.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        return invcExpr.declaration.span.hashCode()
    }
}

class StateModificationOutsideOfPurityBoundaryReporting internal constructor(val assignment: BoundAssignmentStatement, val boundary: SideEffectBoundary) : PurityViolationReporting(
    assignment,
    run {
        val boundaryType = if (boundary.isPure) "purity" else "readonlyness"
        "$boundary cannot assign state outside of its $boundaryType boundary"
    }
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is StateModificationOutsideOfPurityBoundaryReporting) return false

        if (assignment.declaration.span != other.assignment.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        return assignment.declaration.span.hashCode()
    }
}