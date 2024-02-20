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
import compiler.ast.Executable
import compiler.ast.expression.AssignmentExpression
import compiler.binding.BoundExecutable
import compiler.binding.BoundVariable
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.type.BoundTypeReference
import compiler.nullableOr
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrNotReallyAnExpression

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

    override val type: BoundTypeReference?
        get() = valueExpression.type ?: targetExpression.type

    override val isGuaranteedToThrow: Boolean?
        get() = targetExpression.isGuaranteedToThrow nullableOr valueExpression.isGuaranteedToThrow

    private val _modifiedContext = MutableCTContext(context)
    override val modifiedContext: CTContext = _modifiedContext

    override fun semanticAnalysisPhase1() = targetExpression.semanticAnalysisPhase1() + valueExpression.semanticAnalysisPhase1()

    private var resultUsed = false
    override fun markEvaluationResultUsed() {
        resultUsed = true
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        valueExpression.markEvaluationResultUsed()

        val reportings = mutableListOf<Reporting>()
        reportings.addAll(targetExpression.semanticAnalysisPhase2())
        reportings.addAll(valueExpression.semanticAnalysisPhase2())

        if (resultUsed) {
            reportings.add(Reporting.assignmentUsedAsExpression(this))
        }

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableSetOf<Reporting>()

        // TODO
        // reject if the targetExpression does not point to something that
        // can or should be written to
        when (targetExpression) {
            is BoundIdentifierExpression -> {
                reportings.addAll(targetExpression.semanticAnalysisPhase3())
                when (val localReferral = targetExpression.referral) {
                    is BoundIdentifierExpression.ReferringVariable -> {
                        assignmentTargetType = AssignmentTargetType.VARIABLE
                        targetVariable = localReferral.variable

                        val isInitialized = targetVariable!!.isInitializedInContext(context)
                        if (isInitialized) {
                            if (!targetVariable!!.isAssignable) {
                                reportings.add(Reporting.illegalAssignment("Cannot assign to value / final variable ${targetVariable!!.name}", this))
                            }
                        } else {
                            _modifiedContext.markVariableInitialized(targetVariable!!)
                        }

                        localReferral.variable.type?.let { targetType ->
                            valueExpression.type?.evaluateAssignabilityTo(targetType, valueExpression.declaration.sourceLocation)
                                ?.let(reportings::add)
                        }
                    }
                    is BoundIdentifierExpression.ReferringType -> {
                        reportings += Reporting.illegalAssignment("Cannot assign a value to a type", this)
                    }
                    null -> {}
                }
            }

            is BoundMemberAccessExpression -> {
                targetExpression.valueExpression.type?.let { memberOwnerType ->
                    if (!memberOwnerType.mutability.isMutable) {
                        reportings += Reporting.illegalAssignment("Cannot mutate a value of type $memberOwnerType", this)
                    }
                }
                targetExpression.type?.let { targetType ->
                    valueExpression.type?.evaluateAssignabilityTo(targetType, valueExpression.declaration.sourceLocation)
                        ?.let(reportings::add)
                }
            }

            else -> {
                reportings += Reporting.illegalAssignment("Cannot assign to this target", this)
            }
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

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do because assignments are not expressions
    }

    override fun toBackendIr(): IrExpression {
        return IrAssignmentExpressionImpl(
            targetExpression.toBackendIr(),
            valueExpression.toBackendIr(),
        )
    }

    enum class AssignmentTargetType {
        VARIABLE,
        OBJECT_MEMBER
    }
}

/**
 * [BoundAssignmentExpression] is a [BoundExpression] because the compiler wants to detect accidental use of `=` instead
 * of `==`. So [BoundAssignmentExpression.toBackendIr] must return an [IrExpression], as per the [BoundExpression]
 * contract. Consequently, this class must also implement [IrExpression] even though it's not. Unavoidable.
 */
internal class IrAssignmentExpressionImpl(
    override val target: IrExpression,
    override val value: IrExpression,
) : IrAssignmentStatement, IrNotReallyAnExpression