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
import compiler.binding.ObjectMember
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.struct.StructMember
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import io.github.tmarsteel.emerge.backend.api.ir.IrStructMemberAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundMemberAccessExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: MemberAccessExpression,
    val valueExpression: BoundExpression<*>,
    val isNullSafeAccess: Boolean,
    val memberName: String
) : BoundExpression<MemberAccessExpression> {
    /**
     * The type of this expression. Is null before semantic anylsis phase 2 is finished; afterwards is null if the
     * type could not be determined or [memberName] denotes a function.
     */
    override var type: BoundTypeReference? = null
        private set

    /** set in [semanticAnalysisPhase2] */
    var member: ObjectMember? = null
        private set

    override val isGuaranteedToThrow = false // member accessor CAN throw, but must not ALWAYS do so

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return valueExpression.semanticAnalysisPhase1()
    }
    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        valueExpression.markEvaluationResultUsed()

        val reportings = mutableSetOf<Reporting>()
        reportings.addAll(valueExpression.semanticAnalysisPhase2())

        valueExpression.type?.let { valueType ->
            if (valueType.isNullable && !isNullSafeAccess) {
                reportings.add(Reporting.unsafeObjectTraversal(valueExpression, declaration.accessOperatorToken))
                // TODO: set the type of this expression nullable
            }
            else if (!valueType.isNullable && isNullSafeAccess) {
                reportings.add(Reporting.superfluousSafeObjectTraversal(valueExpression, declaration.accessOperatorToken))
            }

            valueType.findMemberVariable(memberName)?.let { member ->
                this.member = member
                this.type = member.type?.instantiateAllParameters(valueType.inherentTypeBindings)
            } ?: run {
                reportings.add(Reporting.unresolvableMemberVariable(this, valueType))
            }
        }

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return valueExpression.semanticAnalysisPhase3()
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
        val memberTemporary = IrCreateTemporaryValueImpl(IrStructMemberAccessExpressionImpl(
            IrTemporaryValueReferenceImpl(baseTemporary),
            (member!! as StructMember).toBackendIr(),
            type!!.toBackendIr(),
        ))

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOf(baseTemporary, memberTemporary)),
            IrTemporaryValueReferenceImpl(memberTemporary),
        )
    }
}

private class IrStructMemberAccessExpressionImpl(
    override val base: IrTemporaryValueReference,
    override val member: IrStruct.Member,
    override val evaluatesTo: IrType,
) : IrStructMemberAccessExpression