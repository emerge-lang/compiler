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
import compiler.binding.BoundFunction
import compiler.binding.BoundStatement
import compiler.binding.classdef.BoundClassMemberVariable
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundInvocationExpression

abstract class PurityViolationReporting protected constructor(
    val violation: BoundStatement<*>,
    message: String
) : Reporting(Level.ERROR, message, violation.declaration.sourceLocation) {
    sealed class Boundary(
        val asString: String,
        /**
         * if true, the boundary is pure. If false it is readonly.
         */
        val isPure: Boolean,
    ) {
        override fun toString() = asString

        class Function(val function: BoundFunction) : Boundary(
            run {
                val modifier = if (function.isDeclaredPure) "pure" else "readonly"
                "$modifier function ${function.name}"
            },
            function.isDeclaredPure,
        )
        class ClassMemberInitializer(val member: BoundClassMemberVariable) : Boundary("member variable initializer", true)
    }
}

data class ReadInPureContextReporting internal constructor(val readingExpression: BoundIdentifierExpression, val boundary: Boundary) : PurityViolationReporting(
    readingExpression,
    "$boundary cannot read ${readingExpression.identifier} (is not within the purity-boundary)"
) {
    override fun toString() = super.toString()
}

data class ImpureInvocationInPureContextReporting internal constructor(val invcExpr: BoundInvocationExpression, val boundary: Boundary) : PurityViolationReporting(
    invcExpr,
    "$boundary cannot invoke impure function ${invcExpr.dispatchedFunction!!.name}"
) {
    override fun toString() = super.toString()
}

data class ModifyingInvocationInReadonlyContextReporting internal constructor(val invcExpr: BoundInvocationExpression, val boundary: Boundary) : PurityViolationReporting(
    invcExpr,
    "$boundary cannot invoke modifying function ${invcExpr.dispatchedFunction!!.name}"
) {
    override fun toString() = super.toString()
}

data class StateModificationOutsideOfPurityBoundaryReporting internal constructor(val assignment: BoundAssignmentStatement, val boundary: Boundary) : PurityViolationReporting(
    assignment,
    run {
        val boundaryType = if (boundary.isPure) "purity" else "readonlyness"
        "$boundary cannot assign state outside of its $boundaryType boundary"
    }
) {
    override fun toString() = super.toString()
}