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

package compiler.diagnostic

import compiler.binding.BoundAssignmentStatement
import compiler.binding.BoundFunction
import compiler.binding.BoundStatement
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.basetype.BoundClassConstructor
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundInvocationExpression

abstract class PurityViolationDiagnostic protected constructor(
    val violation: BoundStatement<*>,
    message: String
) : Diagnostic(Severity.ERROR, message, violation.declaration.span) {
    sealed class SideEffectBoundary(
        val asString: String,
        /**
         * if true, the boundary is pure. If false it is readonly.
         */
        val isPure: Boolean,
    ) {
        override fun toString() = asString

        class Function(val function: BoundFunction) : SideEffectBoundary(
            run {
                val modifier = if (BoundFunction.Purity.PURE.contains(function.purity)) "pure" else "readonly"
                val kindAndName = if (function is BoundClassConstructor) "constructor of class ${function.classDef.simpleName}" else "function ${function.name}"
                "$modifier $kindAndName"
            },
            BoundFunction.Purity.PURE.contains(function.purity),
        )
        class ClassMemberInitializer(val member: BoundBaseTypeMemberVariable) : SideEffectBoundary("member variable initializer", true)
    }
}

class ReadInPureContextDiagnostic internal constructor(val readingExpression: BoundIdentifierExpression, val boundary: SideEffectBoundary) : PurityViolationDiagnostic(
    readingExpression,
    "$boundary cannot read ${readingExpression.identifier} (is not within the purity-boundary)"
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ReadInPureContextDiagnostic) return false

        if (readingExpression.declaration.span != other.readingExpression.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        return readingExpression.declaration.span.hashCode()
    }
}

class ImpureInvocationInPureContextDiagnostic internal constructor(val invcExpr: BoundInvocationExpression, val boundary: SideEffectBoundary) : PurityViolationDiagnostic(
    invcExpr,
    "$boundary cannot invoke impure function ${invcExpr.functionToInvoke!!.name}"
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ImpureInvocationInPureContextDiagnostic) return false

        if (invcExpr.declaration.span != other.invcExpr.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        return invcExpr.declaration.span.hashCode()
    }
}

class ModifyingInvocationInReadonlyContextDiagnostic internal constructor(val invcExpr: BoundInvocationExpression, val boundary: SideEffectBoundary) : PurityViolationDiagnostic(
    invcExpr,
    "$boundary cannot invoke modifying function ${invcExpr.functionToInvoke!!.name}"
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is ModifyingInvocationInReadonlyContextDiagnostic) return false

        if (invcExpr.declaration.span != other.invcExpr.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        return invcExpr.declaration.span.hashCode()
    }
}

class AssignmentOutsideOfPurityBoundaryDiagnostic internal constructor(val assignment: BoundAssignmentStatement, val boundary: SideEffectBoundary) : PurityViolationDiagnostic(
    assignment,
    run {
        val boundaryType = if (boundary.isPure) "purity" else "readonlyness"
        "$boundary cannot change state outside of its $boundaryType boundary"
    }
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is AssignmentOutsideOfPurityBoundaryDiagnostic) return false

        if (assignment.declaration.span != other.assignment.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        return assignment.declaration.span.hashCode()
    }
}

class MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic internal constructor(val expression: BoundExpression<*>, val boundary: SideEffectBoundary) : PurityViolationDiagnostic(
    expression,
    run {
        val boundaryType = if (boundary.isPure) "purity" else "readonlyness"
        "$boundary cannot change state outside of its $boundaryType boundary"
    }
) {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is AssignmentOutsideOfPurityBoundaryDiagnostic) return false

        if (expression.declaration.span != other.assignment.declaration.span) return false

        return true
    }

    override fun hashCode(): Int {
        return expression.declaration.span.hashCode()
    }
}