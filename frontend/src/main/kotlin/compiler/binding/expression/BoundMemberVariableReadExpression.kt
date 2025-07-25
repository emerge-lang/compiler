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

import compiler.ast.AstFunctionAttribute
import compiler.ast.VariableOwnership
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.AccessorKind
import compiler.binding.BoundFunction
import compiler.binding.IrCodeChunkImpl
import compiler.binding.SeanHelper
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.effect.PartialObjectInitialization
import compiler.binding.context.effect.VariableInitialization
import compiler.binding.expression.BoundExpression.Companion.tryAsVariable
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrIsNullExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.AmbiguousInvocationDiagnostic
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnosis.Companion.doWithTransformedFindings
import compiler.diagnostic.FunctionMissingAttributeDiagnostic
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.UnresolvableFunctionOverloadDiagnostic
import compiler.diagnostic.ambiguousMemberVariableRead
import compiler.diagnostic.superfluousSafeObjectTraversal
import compiler.diagnostic.unresolvableMemberVariable
import compiler.diagnostic.unsafeObjectTraversal
import compiler.diagnostic.useOfUninitializedMember
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.api.ir.IrClassFieldAccessExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
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
    private val seanHelper = SeanHelper()
    private var physicalMembers: Set<BoundBaseTypeMemberVariable> = emptySet()
    private val physicalMember: BoundBaseTypeMemberVariable? get() = physicalMembers.firstOrNull()
    private val getterInvocation: BoundInvocationExpression = InvocationExpression(
        declaration,
        null,
        emptyList(),
        declaration.span,
    ).bindTo(context, GetterFilter())

    /**
     * The type of this expression. Is null before semantic analysis phase 2 is finished; remains null afterward if the
     * type could not be determined
     */
    override val type: BoundTypeReference? get() {
        val valueType = valueExpression.type ?: return null

        val nonNullableType = if (physicalMember == null) {
            getterInvocation.type
        } else {
            val rawMemberType = physicalMember!!.type ?: return null
            val instantiatedType = rawMemberType.instantiateAllParameters(valueType.inherentTypeBindings)

            if (physicalMember!!.isDecorated) {
                instantiatedType.withMutability(valueExpression.type?.mutability?.limitedTo(TypeMutability.MUTABLE))
            } else {
                instantiatedType.withMutabilityLimitedTo(valueExpression.type?.mutability)
            }
        }

        return nonNullableType
            ?.withCombinedNullability(if (valueType.isNullable && isNullSafeAccess) TypeReference.Nullability.NULLABLE else TypeReference.Nullability.UNSPECIFIED)
    }

    override val throwBehavior get() = if (physicalMember != null) valueExpression.throwBehavior else getterInvocation.throwBehavior
    override val returnBehavior get() = if (physicalMember != null) valueExpression.returnBehavior else getterInvocation.returnBehavior
    override val modifiedContext = getterInvocation.modifiedContext

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        seanHelper.phase1(diagnosis) {
            valueExpression.semanticAnalysisPhase1(diagnosis)
            valueExpression.markEvaluationResultUsed()
            getterInvocation.semanticAnalysisPhase1(diagnosis)
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        seanHelper.phase2(diagnosis) { phaseCtx ->
            // partially uninitialized is okay as this class verifies that itself
            (valueExpression as? BoundIdentifierExpression)?.allowPartiallyUninitializedValue()
            valueExpression.semanticAnalysisPhase2(diagnosis)

            val valueType = valueExpression.type
            if (valueType == null) {
                phaseCtx.markErroneous()
                return@phase2
            }

            if (valueType.isNullable && !isNullSafeAccess) {
                diagnosis.unsafeObjectTraversal(valueExpression, declaration.accessOperatorToken)
            }
            else if (!valueType.isNullable && isNullSafeAccess) {
                diagnosis.superfluousSafeObjectTraversal(valueExpression, declaration.accessOperatorToken)
            }

            val availableGetters = mutableSetOf<BoundFunction>()
            physicalMembers = valueType.findMemberVariable(memberName)
            physicalMembers.forEach { it.semanticAnalysisPhase2(diagnosis) }
            diagnosis.doWithTransformedFindings(getterInvocation::semanticAnalysisPhase2) { findings ->
                findings.mapNotNull { finding ->
                    if (finding is AmbiguousInvocationDiagnostic && finding.invocation === getterInvocation.declaration) {
                        availableGetters.addAll(finding.candidates)
                        return@mapNotNull null
                    }

                    if (finding is UnresolvableFunctionOverloadDiagnostic && finding.functionNameReference.span == declaration.memberName.span) {
                        availableGetters.clear()
                        return@mapNotNull null
                    }

                    return@mapNotNull if (physicalMembers.isEmpty()) {
                        finding
                    } else {
                        null
                    }
                }
            }
            getterInvocation.functionToInvoke?.let(availableGetters::add)

            if (availableGetters.isEmpty() && physicalMember != null) {
                val isInitialized = valueExpression.tryAsVariable()?.let {
                    context.getEphemeralState(PartialObjectInitialization, it).getMemberInitializationState(physicalMember!!) == VariableInitialization.State.INITIALIZED
                } ?: true

                if (!isInitialized) {
                    diagnosis.useOfUninitializedMember(physicalMember!!, declaration)
                }
            }

            if (availableGetters.size + physicalMembers.size > 1) {
                diagnosis.ambiguousMemberVariableRead(this, physicalMembers, availableGetters)
            }

            if (availableGetters.size + physicalMembers.size == 0) {
                diagnosis.unresolvableMemberVariable(declaration, valueExpression.type)
            }
        }
    }

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        valueExpression.setNothrow(boundary)
    }

    private var usageContextSet = false
    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        check(!usageContextSet)
        usageContextSet = true

        if (physicalMember != null && physicalMember!!.type?.mutability in setOf(null, TypeMutability.READONLY, TypeMutability.IMMUTABLE)) {
            // using the derived value doesn't have an impact on the holder object because the invariants are guaranteed
            // by the member variable type alone, and don't depend on the type of the reference to the holder object
            valueExpression.setEvaluationResultUsage(TransientValueUsage(valueExpression.declaration.span))
            return
        }

        val valueUsedAsType = valueExpression.type
            ?.withMutability(valueUsage.usedAsType?.mutability ?: TypeMutability.READONLY)
        // captured = false here because: the host object isn't being referenced; and the result value is already captured
        // by nature of being stored in an object member, so need to further validate that
        valueExpression.setEvaluationResultUsage(ValueUsage.deriveFromAndThen(
            deriveUsingType = valueUsedAsType,
            deriveWithOwnership = VariableOwnership.BORROWED,
            andThen = valueUsage,
        ))
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        seanHelper.phase3(diagnosis, runIfErrorsPreviously = false) {
            if (physicalMember != null) {
                valueExpression.semanticAnalysisPhase3(diagnosis)
                physicalMember!!.validateAccessFrom(declaration.memberName.span, diagnosis)
            } else {
                getterInvocation.semanticAnalysisPhase3(diagnosis)
            }
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        seanHelper.requirePhase2Done()
        if (seanHelper.phase2HadErrors) {
            return
        }

        valueExpression.visitReadsBeyond(boundary, visitor)
        if (physicalMember == null) {
            getterInvocation.visitReadsBeyond(boundary, visitor)
        }
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        seanHelper.requirePhase2Done()
        if (seanHelper.phase2HadErrors) {
            return
        }

        valueExpression.visitWritesBeyond(boundary, visitor)
        if (physicalMember == null) {
            getterInvocation.visitWritesBeyond(boundary, visitor)
        }
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        // nothing to do, the type of any object member is predetermined;
        // the evaluation result type also must not influence accessor selection
    }

    override val isEvaluationResultReferenceCounted get() = if (physicalMember != null) false else getterInvocation.isEvaluationResultReferenceCounted
    override val isEvaluationResultAnchored get() = if (physicalMember != null) physicalMember!!.isReAssignable == false else getterInvocation.isEvaluationResultAnchored
    override val isCompileTimeConstant get() = valueExpression.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        if (physicalMember == null) {
            return getterInvocation.toBackendIrExpression()
        }

        val code = ArrayList<IrExecutable>(3)
        val baseTemporary = IrCreateTemporaryValueImpl(valueExpression.toBackendIrExpression())
        code.add(baseTemporary)

        val memberTemporary = IrCreateTemporaryValueImpl(IrClassFieldAccessExpressionImpl(
            IrTemporaryValueReferenceImpl(baseTemporary),
            physicalMember!!.field.toBackendIr(),
            type!!.toBackendIr(),
        ))

        val finalTemporary: IrCreateTemporaryValue = if (!valueExpression.type!!.isNullable || !isNullSafeAccess) {
            code.add(memberTemporary)
            memberTemporary
        } else {
            val isBaseNullTemporary = IrCreateTemporaryValueImpl(IrIsNullExpressionImpl(IrTemporaryValueReferenceImpl(baseTemporary), context.swCtx))
            code.add(isBaseNullTemporary)
            val nullableResultType = memberTemporary.type.asNullable()
            val nullLiteral = IrCreateTemporaryValueImpl(IrNullLiteralExpressionImpl(nullableResultType))
            IrCreateTemporaryValueImpl(IrIfExpressionImpl(
                IrTemporaryValueReferenceImpl(isBaseNullTemporary),
                IrImplicitEvaluationExpressionImpl(
                    IrCodeChunkImpl(listOf(nullLiteral)),
                    IrTemporaryValueReferenceImpl(nullLiteral),
                ),
                IrImplicitEvaluationExpressionImpl(
                    IrCodeChunkImpl(listOf(memberTemporary)),
                    IrTemporaryValueReferenceImpl(memberTemporary),
                ),
                nullableResultType,
            ))
        }
        code.add(finalTemporary)

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(code),
            IrTemporaryValueReferenceImpl(finalTemporary),
        )
    }

    private inner class GetterFilter : BoundInvocationExpression.CandidateFilter {
        override fun inspect(candidate: BoundFunction): BoundInvocationExpression.CandidateFilter.Result {
            return if (candidate.attributes.firstAccessorAttribute?.kind == AccessorKind.Read) {
                BoundInvocationExpression.CandidateFilter.Result.Applicable
            } else {
                BoundInvocationExpression.CandidateFilter.Result.Inapplicable(FunctionMissingAttributeDiagnostic(
                    candidate,
                    this@BoundMemberVariableReadExpression.declaration.span,
                    AstFunctionAttribute.Accessor(AccessorKind.Read, KeywordToken(Keyword.GET)),
                    reason = null,
                ))
            }
        }
    }
}

internal class IrClassFieldAccessExpressionImpl(
    override val base: IrTemporaryValueReference,
    override val field: IrClass.Field,
    override val evaluatesTo: IrType,
) : IrClassFieldAccessExpression