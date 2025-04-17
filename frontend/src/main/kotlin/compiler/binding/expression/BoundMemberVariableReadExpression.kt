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
import compiler.ast.VariableOwnership
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.TypeMutability
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SideEffectPrediction
import compiler.binding.SideEffectPrediction.Companion.combineSequentialExecution
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.effect.PartialObjectInitialization
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.expression.BoundExpression.Companion.tryAsVariable
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.superfluousSafeObjectTraversal
import compiler.diagnostic.unsafeObjectTraversal
import compiler.diagnostic.useOfUninitializedMember
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassFieldAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class BoundMemberVariableReadExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: MemberAccessExpression,
    val valueExpression: BoundExpression<*>,
    val isNullSafeAccess: Boolean,
    val memberName: String
) : BoundExpression<MemberAccessExpression> {
    /**
     * The type of this expression. Is null before semantic analysis phase 2 is finished; remains null afterward if the
     * type could not be determined
     */
    override val type: BoundTypeReference?
        get() = if (this::strategy.isInitialized) strategy.evaluationResultType else null

    /** set in [semanticAnalysisPhase2] */
    private lateinit var strategy: Strategy

    override val throwBehavior get() = valueExpression.throwBehavior.combineSequentialExecution(strategy.throwBehaviour)
    override val returnBehavior get() = valueExpression.returnBehavior

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        valueExpression.semanticAnalysisPhase1(diagnosis)
        valueExpression.markEvaluationResultUsed()
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        strategy = NoopStrategy

        // partially uninitialized is okay as this class verifies that itself
        (valueExpression as? BoundIdentifierExpression)?.allowPartiallyUninitializedValue()
        valueExpression.semanticAnalysisPhase2(diagnosis)

        val valueType = valueExpression.type
        if (valueType == null) {
            return
        }

        if (valueType.isNullable && !isNullSafeAccess) {
            diagnosis.unsafeObjectTraversal(valueExpression, declaration.accessOperatorToken)
        }
        else if (!valueType.isNullable && isNullSafeAccess) {
            diagnosis.superfluousSafeObjectTraversal(valueExpression, declaration.accessOperatorToken)
        }

        val member = valueType.findMemberVariable(memberName)
        if (member != null) {
            strategy = DirectReadStrategy(valueType, member)
            strategy.semanticAnalysisPhase2(diagnosis)
            return
        }

        val hiddenInvocation = InvocationExpression(
            declaration,
            null,
            emptyList(),
            declaration.span.deriveGenerated(),
        ).bindTo(context)
        // TODO: trigger unresolvableMemberVariable diagnostic if no setter found
        strategy = AccessorReadStrategy(hiddenInvocation)
        strategy.semanticAnalysisPhase2(diagnosis)
    }

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        valueExpression.setNothrow(boundary)
    }

    private var usageContextSet = false
    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        check(!usageContextSet)
        usageContextSet = true

        val valueUsedAsType = valueExpression.type
            ?.withMutability(TypeMutability.READONLY.union(valueUsage.usedAsType?.mutability ?: TypeMutability.READONLY))
        // captured = false here because: the host object isn't being referenced; and the result value is already captured
        // by nature of being stored in an object member, so need to further validate that
        valueExpression.setEvaluationResultUsage(ValueUsage.deriveFromAndThen(
            deriveUsingType = valueUsedAsType,
            deriveWithOwnership = VariableOwnership.BORROWED,
            andThen = valueUsage,
        ))
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        valueExpression.semanticAnalysisPhase3(diagnosis)
        strategy.semanticAnalysisPhase3(diagnosis)
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

    override val isEvaluationResultReferenceCounted get() = strategy.isEvaluationResultReferenceCounted
    override val isEvaluationResultAnchored get() = valueExpression.isEvaluationResultAnchored && strategy.isEvaluationResultAnchored
    override val isCompileTimeConstant get() = valueExpression.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        return strategy.toBackendIrExpression()
    }

    private interface Strategy {
        /** @see BoundExpression.throwBehavior */
        val throwBehaviour: SideEffectPrediction?
        /** @see BoundExpression.type */
        val evaluationResultType: BoundTypeReference?
        /** @see BoundExpression.isEvaluationResultAnchored */
        val isEvaluationResultAnchored: Boolean
        /** @see BoundExpression.isEvaluationResultReferenceCounted */
        val isEvaluationResultReferenceCounted: Boolean
        /** @see BoundExpression.semanticAnalysisPhase2 */
        fun semanticAnalysisPhase2(diagnosis: Diagnosis) = Unit
        /** @see BoundExpression.semanticAnalysisPhase3 */
        fun semanticAnalysisPhase3(diagnosis: Diagnosis) = Unit
        /** @see BoundExpression.toBackendIrExpression */
        fun toBackendIrExpression(): IrExpression
    }
    inner class DirectReadStrategy(valueType: BoundTypeReference, val member: BoundBaseTypeMemberVariable) : Strategy {
        override val throwBehaviour = SideEffectPrediction.NEVER
        override val evaluationResultType: BoundTypeReference? = member.type
            ?.instantiateAllParameters(valueType.inherentTypeBindings)
            ?.withMutabilityLimitedTo(valueExpression.type?.mutability)
        override val isEvaluationResultAnchored = member.isReAssignable == false
        override val isEvaluationResultReferenceCounted = false

        override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
            this.evaluationResultType

            val isInitialized = valueExpression.tryAsVariable()?.let {
                context.getEphemeralState(PartialObjectInitialization, it).getMemberInitializationState(member) == VariableInitialization.State.INITIALIZED
            } ?: true

            if (!isInitialized) {
                diagnosis.useOfUninitializedMember(member, declaration)
            }
        }

        override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
            member.validateAccessFrom(declaration.memberName.span, diagnosis)
        }

        override fun toBackendIrExpression(): IrExpression {
            val baseTemporary = IrCreateTemporaryValueImpl(valueExpression.toBackendIrExpression())
            val memberTemporary = IrCreateTemporaryValueImpl(IrClassFieldAccessExpressionImpl(
                IrTemporaryValueReferenceImpl(baseTemporary),
                member.field.toBackendIr(),
                evaluationResultType!!.toBackendIr(),
            ))

            return IrImplicitEvaluationExpressionImpl(
                IrCodeChunkImpl(listOf(baseTemporary, memberTemporary)),
                IrTemporaryValueReferenceImpl(memberTemporary),
            )
        }
    }

    inner class AccessorReadStrategy(val hiddenInvocation: BoundInvocationExpression) : Strategy {
        override val throwBehaviour: SideEffectPrediction? get()= hiddenInvocation.throwBehavior
        override val evaluationResultType: BoundTypeReference? get()= hiddenInvocation.type
        override val isEvaluationResultAnchored = hiddenInvocation.isEvaluationResultAnchored
        override val isEvaluationResultReferenceCounted = hiddenInvocation.isEvaluationResultReferenceCounted

        override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
            hiddenInvocation.semanticAnalysisPhase1(diagnosis)
            hiddenInvocation.semanticAnalysisPhase2(diagnosis)
        }

        override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
            hiddenInvocation.semanticAnalysisPhase3(diagnosis)
        }

        override fun toBackendIrExpression(): IrExpression {
            return hiddenInvocation.toBackendIrExpression()
        }
    }

    /**
     * to be used when other errors in the input code prevent determining the correct strategy to use;
     * behaves as nutrally as possible, thereby trying not to trigger any more diagnostics
     */
    private object NoopStrategy : Strategy {
        override val throwBehaviour = SideEffectPrediction.NEVER
        override val evaluationResultType = null
        override val isEvaluationResultAnchored = true
        override val isEvaluationResultReferenceCounted = false
        override fun toBackendIrExpression(): IrExpression {
            throw InternalCompilerError("This should be unreachable!")
        }
    }
}

internal class IrClassFieldAccessExpressionImpl(
    override val base: IrTemporaryValueReference,
    override val field: IrClass.Field,
    override val evaluatesTo: IrType,
) : IrClassFieldAccessExpression