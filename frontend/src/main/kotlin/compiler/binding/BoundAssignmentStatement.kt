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

package compiler.binding

import compiler.OnceAction
import compiler.ast.AssignmentStatement
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundIdentifierExpression
import compiler.binding.expression.BoundMemberAccessExpression
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropReferenceStatementImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.IrGenericTypeReferenceImpl
import compiler.binding.type.IrParameterizedTypeImpl
import compiler.binding.type.IrSimpleTypeImpl
import compiler.binding.type.PartiallyInitializedType
import compiler.nullableOr
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrAssignmentStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrGenericTypeReference
import io.github.tmarsteel.emerge.backend.api.ir.IrParameterizedType
import io.github.tmarsteel.emerge.backend.api.ir.IrSimpleType
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrVariableDeclaration
import kotlin.properties.Delegates

class BoundAssignmentStatement(
    override val context: ExecutionScopedCTContext,
    override val declaration: AssignmentStatement,
    val targetExpression: BoundExpression<*>,
    val toAssignExpression: BoundExpression<*>
) : BoundStatement<AssignmentStatement> {
    override val isGuaranteedToThrow: Boolean?
        get() = targetExpression.isGuaranteedToThrow nullableOr toAssignExpression.isGuaranteedToThrow

    private val _modifiedContext = MutableExecutionScopedCTContext.deriveFrom(context)
    override val modifiedContext: ExecutionScopedCTContext = _modifiedContext

    override val implicitEvaluationResultType: BoundTypeReference? = null

    init {
        if (targetExpression is BoundMemberAccessExpression) {
            targetExpression.usageContext = BoundMemberAccessExpression.UsageContext.WRITE
        }
    }

    private val onceAction = OnceAction()

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase1) {
            val reportings = mutableListOf<Reporting>()
            reportings.addAll(targetExpression.semanticAnalysisPhase1())
            reportings.addAll(toAssignExpression.semanticAnalysisPhase1())

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

            reportings
        }
    }

    private var implicitEvaluationRequired = false
    override fun requireImplicitEvaluationTo(type: BoundTypeReference) {
        implicitEvaluationRequired = true
    }

    /** set in [semanticAnalysisPhase2], null if it cannot be determined */
    private var target: AssignmentTarget? = null

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase2) {
            toAssignExpression.markEvaluationResultUsed()
            target?.type?.let(toAssignExpression::setExpectedEvaluationResultType)

            val reportings = mutableListOf<Reporting>()
            reportings.addAll(targetExpression.semanticAnalysisPhase2())
            reportings.addAll(toAssignExpression.semanticAnalysisPhase2())
            target?.semanticAnalysisPhase2()?.let(reportings::addAll)

            if (implicitEvaluationRequired) {
                reportings.add(Reporting.assignmentUsedAsExpression(this))
            }

            reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return onceAction.getResult(OnceAction.SemanticAnalysisPhase3) {
            val reportings = mutableSetOf<Reporting>()
            reportings.addAll(targetExpression.semanticAnalysisPhase3())
            reportings.addAll(toAssignExpression.semanticAnalysisPhase3())
            target?.semanticAnalysisPhase3()?.let(reportings::addAll)

            reportings
        }
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        val targetReads = target?.findReadsBeyond(boundary) ?: emptyList()
        return targetReads + toAssignExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        val targetWrites = target?.findWritesBeyond(boundary) ?: emptyList()
        return targetWrites + toAssignExpression.findWritesBeyond(boundary)
    }

    override fun toBackendIrStatement(): IrExecutable {
        return target!!.toBackendIrExecutable()
    }

    sealed interface AssignmentTarget {
        val type: BoundTypeReference?
        fun semanticAnalysisPhase2(): Collection<Reporting>
        fun semanticAnalysisPhase3(): Collection<Reporting>
        fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>>
        fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>>
        fun toBackendIrExecutable(): IrExecutable
    }

    inner class VariableTarget(val reference: BoundIdentifierExpression.ReferringVariable) : AssignmentTarget {
        override val type get() = reference.variable.type

        override fun semanticAnalysisPhase2(): Collection<Reporting> {
            return emptySet()
        }

        private lateinit var initializationState: VariableInitialization.State
        override fun semanticAnalysisPhase3(): Collection<Reporting> {
            val reportings = mutableListOf<Reporting>()

            initializationState = reference.variable.getInitializationStateInContext(this@BoundAssignmentStatement.context)
            if (initializationState == VariableInitialization.State.NOT_INITIALIZED || initializationState == VariableInitialization.State.MAYBE_INITIALIZED) {
                _modifiedContext.trackSideEffect(VariableInitialization.WriteToVariableEffect(reference.variable))
            }
            if (initializationState == VariableInitialization.State.MAYBE_INITIALIZED) {
                if (reference.variable.isReAssignable) {
                    _modifiedContext.trackSideEffect(VariableInitialization.WriteToVariableEffect(reference.variable))
                } else {
                    reportings.add(Reporting.illegalAssignment("Variable ${reference.variable.name} may have already been initialized, cannot assign a value again", this@BoundAssignmentStatement))
                }
            }
            if (initializationState == VariableInitialization.State.INITIALIZED) {
                if (!reference.variable.isReAssignable) {
                    reportings.add(Reporting.illegalAssignment("Variable ${reference.variable.name} is already initialized, cannot re-assign", this@BoundAssignmentStatement))
                }
            }

            reference.variable.type?.let { targetType ->
                toAssignExpression.type?.evaluateAssignabilityTo(targetType, toAssignExpression.declaration.sourceLocation)
                    ?.let(reportings::add)
            }

            return reportings
        }

        override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
            // we are writing to the variable, not reading from it
            return emptySet()
        }

        override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
            if (context.containsWithinBoundary(reference.variable, boundary)) {
                return emptyList()
            }

            return listOf(this@BoundAssignmentStatement)
        }

        override fun toBackendIrExecutable(): IrExecutable {
            val dropPreviousCode: List<IrExecutable> = when (initializationState) {
                VariableInitialization.State.NOT_INITIALIZED -> emptyList()
                else -> {
                    var previousType = reference.variable.getTypeInContext(context)!!.toBackendIr()
                    if (initializationState == VariableInitialization.State.MAYBE_INITIALIZED) {
                        // forces a null-check on the reference drop, preventing a null-pointer dereference when a maybe-initialized
                        // variable of a non-null type is being assigned to
                        previousType = previousType.nullable()
                    }
                    val previousTemporary = IrCreateTemporaryValueImpl(
                        IrVariableAccessExpressionImpl(reference.variable.backendIrDeclaration),
                        previousType,
                    )
                    listOf(previousTemporary, IrDropReferenceStatementImpl(previousTemporary))
                }
            }

            val toAssignTemporary = IrCreateTemporaryValueImpl(toAssignExpression.toBackendIrExpression())
            val assignStatement = IrAssignmentStatementImpl(
                IrAssignmentStatementTargetVariableImpl(reference.variable.backendIrDeclaration),
                IrTemporaryValueReferenceImpl(toAssignTemporary),
            )

            return IrCodeChunkImpl(dropPreviousCode + listOf(
                toAssignTemporary,
                assignStatement
            ))
        }
    }

    inner class ObjectMemberTarget(
        val memberAccess: BoundMemberAccessExpression,
    ) : AssignmentTarget {
        override val type get() = memberAccess.type

        override fun semanticAnalysisPhase2(): Collection<Reporting> {
            (memberAccess.valueExpression as? BoundIdentifierExpression)
                ?.referral?.let { it as? BoundIdentifierExpression.ReferringVariable }
                ?.variable
                ?.let { assignedToVar ->
                    val member = memberAccess.member
                    if (member != null) {
                        _modifiedContext.markVariableInitializationCompletedPartially(assignedToVar, member)
                    }
                }

            return emptySet()
        }

        private var memberIsPotentiallyUninitialized by Delegates.notNull<Boolean>()

        override fun semanticAnalysisPhase3(): Collection<Reporting> {
            val valueType = memberAccess.valueExpression.type
            memberIsPotentiallyUninitialized = (valueType as? PartiallyInitializedType)
                ?.uninitializedMemberVariables
                ?.contains(memberAccess.member!!)
                ?: false

            val reportings = mutableListOf<Reporting>()

            memberAccess.valueExpression.type?.let { memberOwnerType ->
                if (!memberOwnerType.mutability.isMutable) {
                    reportings += Reporting.illegalAssignment("Cannot mutate a value of type $memberOwnerType", this@BoundAssignmentStatement)
                }
            }
            memberAccess.type?.let { targetType ->
                toAssignExpression.type?.evaluateAssignabilityTo(targetType, toAssignExpression.declaration.sourceLocation)
                    ?.let(reportings::add)
            }

            if (!memberIsPotentiallyUninitialized && memberAccess.member?.isReAssignable == false) {
                reportings.add(Reporting.illegalAssignment("Member variable ${memberAccess.member!!.name} cannot be re-assigned", this@BoundAssignmentStatement))
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

            return listOf(this@BoundAssignmentStatement)
        }

        override fun toBackendIrExecutable(): IrExecutable {
            val dropPreviousReferenceCode: IrCodeChunk
            if (memberAccess.member!!.isReAssignable) {
                var previousType = memberAccess.type!!.toBackendIr()
                if (memberIsPotentiallyUninitialized) {
                    // forces a null-check on the reference drop, which prevents a nullpointer deref for an empty object
                    previousType = previousType.nullable()
                }
                val previousTemporary = IrCreateTemporaryValueImpl(memberAccess.toBackendIrExpression(), previousType)
                dropPreviousReferenceCode = IrCodeChunkImpl(listOf(
                    previousTemporary,
                    IrDropReferenceStatementImpl(previousTemporary),
                ))
            } else {
                check(memberIsPotentiallyUninitialized) { "multiple assignments to a non-reassignable target" }
                // this is the first and only assignment, no need to drop a previous reference
                dropPreviousReferenceCode = IrCodeChunkImpl(emptyList())
            }

            val baseTemporary = IrCreateTemporaryValueImpl(memberAccess.valueExpression.toBackendIrExpression())
            val baseTemporaryRefIncrement = IrCreateReferenceStatementImpl(baseTemporary).takeUnless { memberAccess.valueExpression.isEvaluationResultReferenceCounted }
            val toAssignTemporary = IrCreateTemporaryValueImpl(toAssignExpression.toBackendIrExpression())
            val toAssignTemporaryRefIncrement = IrCreateReferenceStatementImpl(toAssignTemporary).takeUnless { toAssignExpression.isEvaluationResultReferenceCounted }

            return IrCodeChunkImpl(listOfNotNull(
                dropPreviousReferenceCode,
                baseTemporary,
                baseTemporaryRefIncrement,
                toAssignTemporary,
                toAssignTemporaryRefIncrement,
                IrAssignmentStatementImpl(
                    IrAssignmentStatementTargetClassMemberVariableImpl(
                        memberAccess.member!!.toBackendIr(),
                        IrTemporaryValueReferenceImpl(baseTemporary),
                    ),
                    IrTemporaryValueReferenceImpl(toAssignTemporary),
                ),
                IrDropReferenceStatementImpl(baseTemporary),
            ))
        }
    }
}

/**
 * [BoundAssignmentStatement] is a [BoundExpression] because the compiler wants to detect accidental use of `=` instead
 * of `==`. So [BoundAssignmentStatement.toBackendIrStatement] must return an [IrExpression], as per the [BoundExpression]
 * contract. Consequently, this class must also implement [IrExpression] even though it's not. Unavoidable.
 */
internal class IrAssignmentStatementImpl(
    override val target: IrAssignmentStatement.Target,
    override val value: IrTemporaryValueReference,
) : IrAssignmentStatement

internal class IrAssignmentStatementTargetVariableImpl(
    override val declaration: IrVariableDeclaration,
): IrAssignmentStatement.Target.Variable

internal class IrAssignmentStatementTargetClassMemberVariableImpl(
    override val memberVariable: IrClass.MemberVariable,
    override val objectValue: IrTemporaryValueReference,
) : IrAssignmentStatement.Target.ClassMemberVariable

private fun IrType.nullable(): IrType = if (isNullable) this else when (this) {
    is IrSimpleType -> IrSimpleTypeImpl(this.baseType, true)
    is IrGenericTypeReference -> IrGenericTypeReferenceImpl(this.parameter, effectiveBound.nullable())
    is IrParameterizedType -> IrParameterizedTypeImpl(this.simpleType.nullable() as IrSimpleType, arguments)
}