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
import compiler.binding.BoundStatement
import compiler.binding.BoundVariable
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.CTContext
import compiler.binding.context.MutableCTContext
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.struct.StructMember
import compiler.binding.type.BoundTypeReference
import compiler.nullableOr
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration

class BoundAssignmentExpression(
    override val context: CTContext,
    override val declaration: AssignmentExpression,
    val targetExpression: BoundExpression<*>,
    val valueExpression: BoundExpression<*>
) : BoundExpression<AssignmentExpression> {
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

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        reportings.addAll(targetExpression.semanticAnalysisPhase1())
        reportings.addAll(valueExpression.semanticAnalysisPhase1())

        target = when (targetExpression) {
            is BoundIdentifierExpression -> when (val ref = targetExpression.referral) {
                is BoundIdentifierExpression.ReferringVariable -> VariableTarget(ref)
                is BoundIdentifierExpression.ReferringType -> {
                    reportings += Reporting.illegalAssignment("Cannot assign a value to a type", this)
                    null
                }
                null -> null
            }
            is BoundMemberAccessExpression -> ObjectMemberTarget(targetExpression)
            else -> {
                reportings += Reporting.illegalAssignment("Cannot assign to this target", this)
                null
            }
        }

        return reportings
    }

    private var resultUsed = false
    override fun markEvaluationResultUsed() {
        resultUsed = true
    }

    /** set in [semanticAnalysisPhase2], null if it cannot be determined */
    private var target: AssignmentTarget? = null

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
        reportings.addAll(targetExpression.semanticAnalysisPhase3())
        reportings.addAll(valueExpression.semanticAnalysisPhase3())
        target?.semanticAnalysisPhase3()?.let(reportings::addAll)

        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        val targetReads = target?.findReadsBeyond(boundary) ?: emptyList()
        return targetReads + valueExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        val targetWrites = target?.findWritesBeyond(boundary) ?: emptyList()
        return targetWrites + valueExpression.findWritesBeyond(boundary)
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do because assignments are not expressions
    }

    override fun toBackendIrStatement(): IrExecutable {
        return target!!.toBackendIrExecutable(valueExpression)
    }

    override fun toBackendIrExpression(): IrExpression {
        throw InternalCompilerError("Assignment used as expression made it to the code generation phase - should have been stopped in semantic analysis")
    }

    sealed interface AssignmentTarget {
        fun semanticAnalysisPhase3(): Collection<Reporting>
        fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>>
        fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>>
        fun toBackendIrExecutable(toAssign: BoundExpression<*>): IrExecutable
    }

    inner class VariableTarget(val reference: BoundIdentifierExpression.ReferringVariable) : AssignmentTarget {
        override fun semanticAnalysisPhase3(): Collection<Reporting> {
            val reportings = mutableListOf<Reporting>()

            val isInitialized = reference.variable.isInitializedInContext(this@BoundAssignmentExpression.context)
            if (isInitialized) {
                if (!targetVariable!!.isAssignable) {
                    reportings.add(Reporting.illegalAssignment("Cannot assign to value / final variable ${targetVariable!!.name}", this@BoundAssignmentExpression))
                }
            } else {
                _modifiedContext.markVariableInitialized(targetVariable!!)
            }

            reference.variable.type?.let { targetType ->
                valueExpression.type?.evaluateAssignabilityTo(targetType, valueExpression.declaration.sourceLocation)
                    ?.let(reportings::add)
            }

            return reportings
        }

        override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
            return reference.findReadsBeyond(boundary)
        }

        override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
            if (context.containsWithinBoundary(reference.variable, boundary)) {
                return emptyList()
            }

            return listOf(this@BoundAssignmentExpression)
        }

        override fun toBackendIrExecutable(toAssign: BoundExpression<*>): IrExecutable {
            val toAssignTemporary = IrCreateTemporaryValueImpl(toAssign.toBackendIrExpression())
            return IrCodeChunkImpl(listOf(
                toAssignTemporary,
                IrAssignmentStatementImpl(
                    IrAssignmentStatementTargetVariableImpl(reference.variable.backendIrDeclaration),
                    IrTemporaryValueReferenceImpl(toAssignTemporary),
                )
            ))
        }
    }

    inner class ObjectMemberTarget(
        val memberAccess: BoundMemberAccessExpression,
    ) : AssignmentTarget {
        override fun semanticAnalysisPhase3(): Collection<Reporting> {
            val reportings = mutableListOf<Reporting>()

            memberAccess.valueExpression.type?.let { memberOwnerType ->
                if (!memberOwnerType.mutability.isMutable) {
                    reportings += Reporting.illegalAssignment("Cannot mutate a value of type $memberOwnerType", this@BoundAssignmentExpression)
                }
            }
            memberAccess.type?.let { targetType ->
                valueExpression.type?.evaluateAssignabilityTo(targetType, valueExpression.declaration.sourceLocation)
                    ?.let(reportings::add)
            }

            return reportings
        }

        override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
            return memberAccess.valueExpression.findReadsBeyond(boundary)
        }

        override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
            if (memberAccess.valueExpression.findReadsBeyond(boundary).isEmpty()) {
                return emptyList()
            }

            return listOf(this@BoundAssignmentExpression)
        }

        override fun toBackendIrExecutable(toAssign: BoundExpression<*>): IrExecutable {
            // TODO refcount the base while the temporary is potentially dropping the last reference to it!
            val baseTemporary = IrCreateTemporaryValueImpl(memberAccess.valueExpression.toBackendIrExpression())
            val toAssignTemporary = IrCreateTemporaryValueImpl(toAssign.toBackendIrExpression())
            return IrCodeChunkImpl(listOf(
                baseTemporary,
                toAssignTemporary,
                IrAssignmentStatementImpl(
                    IrAssignmentStatementTargetStructMemberImpl(
                        (memberAccess.member as StructMember).toBackendIr(),
                        IrTemporaryValueReferenceImpl(baseTemporary),
                    ),
                    IrTemporaryValueReferenceImpl(baseTemporary),
                )
            ))
        }
    }
}

/**
 * [BoundAssignmentExpression] is a [BoundExpression] because the compiler wants to detect accidental use of `=` instead
 * of `==`. So [BoundAssignmentExpression.toBackendIrStatement] must return an [IrExpression], as per the [BoundExpression]
 * contract. Consequently, this class must also implement [IrExpression] even though it's not. Unavoidable.
 */
internal class IrAssignmentStatementImpl(
    override val target: IrAssignmentStatement.Target,
    override val value: IrTemporaryValueReference,
) : IrAssignmentStatement

internal class IrAssignmentStatementTargetVariableImpl(
    override val declaration: IrVariableDeclaration,
): IrAssignmentStatement.Target.Variable

private class IrAssignmentStatementTargetStructMemberImpl(
    override val member: IrStruct.Member,
    override val structValue: IrTemporaryValueReference,
) : IrAssignmentStatement.Target.StructMember