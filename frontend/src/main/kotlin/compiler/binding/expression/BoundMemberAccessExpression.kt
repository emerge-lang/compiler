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

import compiler.ast.expression.MemberAccessExpression
import compiler.binding.BoundStatement
import compiler.binding.IrCodeChunkImpl
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.effect.PartialObjectInitialization
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.expression.BoundExpression.Companion.tryAsVariable
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassMemberVariableAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundMemberAccessExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: MemberAccessExpression,
    val valueExpression: BoundExpression<*>,
    val isNullSafeAccess: Boolean,
    val memberName: String
) : BoundExpression<MemberAccessExpression> {
    var usageContext: UsageContext = UsageContext.READ

    /**
     * The type of this expression. Is null before semantic anylsis phase 2 is finished; afterwards is null if the
     * type could not be determined or [memberName] denotes a function.
     */
    override var type: BoundTypeReference? = null
        private set

    /** set in [semanticAnalysisPhase2] */
    var member: BoundBaseTypeMemberVariable? = null
        private set

    override val throwBehavior get() = valueExpression.throwBehavior
    override val returnBehavior get() = valueExpression.returnBehavior

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = valueExpression.semanticAnalysisPhase1()
        valueExpression.markEvaluationResultUsed()
        return reportings
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        // partially uninitialized is okay as this class verifies that itself
        (valueExpression as? BoundIdentifierExpression)?.allowPartiallyUninitializedValue()

        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(valueExpression.semanticAnalysisPhase2())

        val valueType = valueExpression.type
        if (valueType != null) {
            if (valueType.isNullable && !isNullSafeAccess) {
                reportings.add(Reporting.unsafeObjectTraversal(valueExpression, declaration.accessOperatorToken))
            }
            else if (!valueType.isNullable && isNullSafeAccess) {
                reportings.add(Reporting.superfluousSafeObjectTraversal(valueExpression, declaration.accessOperatorToken))
            }

            val member = valueType.findMemberVariable(memberName)
            if (member == null) {
                reportings.add(Reporting.unresolvableMemberVariable(this, valueType))
            } else {
                this.member = member
                this.type = member.type?.instantiateAllParameters(valueType.inherentTypeBindings)

                if (usageContext.requiresMemberInitialized) {
                    val isInitialized = valueExpression.tryAsVariable()?.let {
                        context.getEphemeralState(PartialObjectInitialization, it).getMemberInitializationState(member) == VariableInitialization.State.INITIALIZED
                    } ?: true

                    if (!isInitialized) {
                        reportings.add(Reporting.useOfUninitializedMember(this))
                    }
                }
            }
        }

        return reportings
    }

    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        valueExpression.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        reportings.addAll(valueExpression.semanticAnalysisPhase3())
        member?.let { resolvedMember ->
            reportings.addAll(
                resolvedMember.validateAccessFrom(declaration.memberName.span)
            )
        }
        return reportings
    }

    override fun findReadsBeyond(boundary: CTContext): Collection<BoundExpression<*>> {
        return valueExpression.findReadsBeyond(boundary)
    }

    override fun findWritesBeyond(boundary: CTContext): Collection<BoundStatement<*>> {
        return valueExpression.findWritesBeyond(boundary)
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference) {
        // nothing to do, the type of any object member is predetermined
    }

    override val isEvaluationResultReferenceCounted = false
    override val isCompileTimeConstant get() = valueExpression.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        val baseTemporary = IrCreateTemporaryValueImpl(valueExpression.toBackendIrExpression())
        val memberTemporary = IrCreateTemporaryValueImpl(IrClassMemberVariableAccessExpressionImpl(
            IrTemporaryValueReferenceImpl(baseTemporary),
            member!!.toBackendIr(),
            type!!.toBackendIr(),
        ))

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOf(baseTemporary, memberTemporary)),
            IrTemporaryValueReferenceImpl(memberTemporary),
        )
    }

    enum class UsageContext(val requiresMemberInitialized: Boolean) {
        READ(true),
        WRITE(false),
        ;
    }
}

internal class IrClassMemberVariableAccessExpressionImpl(
    override val base: IrTemporaryValueReference,
    override val memberVariable: IrClass.MemberVariable,
    override val evaluatesTo: IrType,
) : IrClassMemberVariableAccessExpression