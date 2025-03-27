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
import compiler.ast.type.TypeMutability
import compiler.binding.ImpurityVisitor
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
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.superfluousSafeObjectTraversal
import compiler.diagnostic.unresolvableMemberVariable
import compiler.diagnostic.unsafeObjectTraversal
import compiler.diagnostic.useOfUninitializedMember
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassFieldAccessExpression
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

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        valueExpression.semanticAnalysisPhase1(diagnosis)
        valueExpression.markEvaluationResultUsed()
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        // partially uninitialized is okay as this class verifies that itself
        (valueExpression as? BoundIdentifierExpression)?.allowPartiallyUninitializedValue()
        valueExpression.semanticAnalysisPhase2(diagnosis)

        val valueType = valueExpression.type
        if (valueType != null) {
            if (valueType.isNullable && !isNullSafeAccess) {
                diagnosis.unsafeObjectTraversal(valueExpression, declaration.accessOperatorToken)
            }
            else if (!valueType.isNullable && isNullSafeAccess) {
                diagnosis.superfluousSafeObjectTraversal(valueExpression, declaration.accessOperatorToken)
            }

            val member = valueType.findMemberVariable(memberName)
            if (member == null) {
                diagnosis.unresolvableMemberVariable(this, valueType)
            } else {
                this.member = member
                this.type = member.type
                    ?.instantiateAllParameters(valueType.inherentTypeBindings)
                    ?.withLimitedMutability(valueExpression.type?.mutability)

                if (usageContext.requiresMemberInitialized) {
                    val isInitialized = valueExpression.tryAsVariable()?.let {
                        context.getEphemeralState(PartialObjectInitialization, it).getMemberInitializationState(member) == VariableInitialization.State.INITIALIZED
                    } ?: true

                    if (!isInitialized) {
                        diagnosis.useOfUninitializedMember(this)
                    }
                }
            }
        }
    }

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        valueExpression.setNothrow(boundary)
    }

    private var usageContextSet = false
    override fun setUsageContext(usedAsType: BoundTypeReference) {
        check(!usageContextSet)
        usageContextSet = true

        val usageBaseType = valueExpression.type ?: context.swCtx.unresolvableReplacementType
        val usedWithMutability = usageContext.mutability.union(usedAsType.mutability)
        valueExpression.setUsageContext(usageBaseType.withMutability(usedWithMutability))
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        valueExpression.semanticAnalysisPhase3(diagnosis)
        member?.validateAccessFrom(declaration.memberName.span, diagnosis)
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        valueExpression.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        valueExpression.visitWritesBeyond(boundary, visitor)
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        // nothing to do, the type of any object member is predetermined
    }

    override val isEvaluationResultReferenceCounted = false
    override val isEvaluationResultAnchored get() = valueExpression.isEvaluationResultAnchored && member?.isReAssignable == false
    override val isCompileTimeConstant get() = valueExpression.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        val baseTemporary = IrCreateTemporaryValueImpl(valueExpression.toBackendIrExpression())
        val memberTemporary = IrCreateTemporaryValueImpl(IrClassFieldAccessExpressionImpl(
            IrTemporaryValueReferenceImpl(baseTemporary),
            member!!.field.toBackendIr(),
            type!!.toBackendIr(),
        ))

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOf(baseTemporary, memberTemporary)),
            IrTemporaryValueReferenceImpl(memberTemporary),
        )
    }

    enum class UsageContext(
        val requiresMemberInitialized: Boolean,
        val mutability: TypeMutability,
    ) {
        READ(true, TypeMutability.READONLY),
        WRITE(false, TypeMutability.MUTABLE),
        ;
    }
}

internal class IrClassFieldAccessExpressionImpl(
    override val base: IrTemporaryValueReference,
    override val field: IrClass.Field,
    override val evaluatesTo: IrType,
) : IrClassFieldAccessExpression