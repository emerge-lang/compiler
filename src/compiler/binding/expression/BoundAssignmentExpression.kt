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

import compiler.InternalCompilerError
import compiler.ast.expression.AssignmentExpression
import compiler.ast.Executable
import compiler.binding.BoundExecutable
import compiler.binding.BoundVariable
import compiler.binding.context.CTContext
import compiler.binding.type.ResolvedTypeReference
import compiler.nullableOr
import compiler.reportings.Reporting

class BoundAssignmentExpression(
    override val context: CTContext,
    override val declaration: AssignmentExpression,
    val targetExpression: BoundExpression<*>,
    val valueExpression: BoundExpression<*>
) : BoundExpression<AssignmentExpression> {

    /**
     * What this statement assigns to. Must not be null after semantic analysis has been completed.
     */
    var assignmentTargetType: AssignmentTargetType? = null
        private set

    /**
     * The variable this statement assigns to, if it does assign to a variable (see [assignmentTargetType])
     */
    var targetVariable: BoundVariable? = null
        private set

    override val type: ResolvedTypeReference?
        get() = valueExpression.type ?: targetExpression.type

    override val isGuaranteedToThrow: Boolean?
        get() = targetExpression.isGuaranteedToThrow nullableOr valueExpression.isGuaranteedToThrow

    override fun semanticAnalysisPhase1() = targetExpression.semanticAnalysisPhase1() + valueExpression.semanticAnalysisPhase1()

    override fun semanticAnalysisPhase2() = targetExpression.semanticAnalysisPhase2() + valueExpression.semanticAnalysisPhase2()

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // TODO
        // reject if the targetExpression does not point to something that
        // can or should be written to
        if (targetExpression is BoundIdentifierExpression) {
            reportings.addAll(targetExpression.semanticAnalysisPhase3())
            when (targetExpression.referredType) {
                BoundIdentifierExpression.ReferredType.VARIABLE -> {
                    assignmentTargetType = AssignmentTargetType.VARIABLE
                    targetVariable = targetExpression.referredVariable!!

                    if (!targetVariable!!.isAssignable) {
                        reportings.add(Reporting.illegalAssignment("Cannot assign to value / final variable ${targetVariable!!.name}", this))
                    }
                }
                BoundIdentifierExpression.ReferredType.TYPENAME -> {
                    reportings += Reporting.illegalAssignment("Cannot assign a value to a type", this)
                }
                else -> {}
            }
        }
        else if (targetExpression is BoundMemberAccessExpression) {
            targetExpression.valueExpression.type?.let { memberOwnerType ->
                if (!memberOwnerType.mutability.isMutable) {
                    reportings += Reporting.illegalAssignment("Cannot mutate a value of type $memberOwnerType", this)
                }
            }
        }
        else {
            reportings += Reporting.illegalAssignment("Cannot assign to this target", this)
        }

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        return valueExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundExecutable<Executable<*>>> {
        val writesByValueExpression = valueExpression.findWritesBeyond(boundary)

        when (assignmentTargetType) {
            AssignmentTargetType.VARIABLE -> {
                if (context.containsWithinBoundary(targetVariable!!, boundary)) {
                    return writesByValueExpression
                }
                else {
                    return writesByValueExpression + this
                }
            }
            null -> {
                return writesByValueExpression
                /* could not be determined, should have produced an ERROR reporting earlier*/
            }
            else -> throw InternalCompilerError("Write boundary check for $assignmentTargetType not implemented yet")
        }
    }

    enum class AssignmentTargetType {
        VARIABLE,
        OBJECT_MEMBER
    }
}