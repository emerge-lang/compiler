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

import compiler.ast.AstCodeChunk
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.effect.CallFrameExit
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.IrStaticDispatchFunctionInvocationImpl
import compiler.binding.expression.ValueUsage
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateStrongReferenceStatementImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.misc_ir.IrUpdateSourceLocationStatementImpl
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.implicitlyEvaluatingAStatement
import compiler.handleCyclicInvocation
import compiler.util.mapToBackendIrWithDebugLocations
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateStrongReferenceStatement
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

class BoundCodeChunk(
    /**
     * Context that applies to the leftHandSide statement; derivatives are stored within the statements themselves
     */
    override val context: ExecutionScopedCTContext,

    override val declaration: AstCodeChunk,

    val statements: List<BoundExecutable<*>>,
) : BoundExpression<AstCodeChunk> {
    private val lastStatementAsExpression = statements.lastOrNull() as? BoundExpression<*>

    override var type: BoundTypeReference? = null

    override val isNoop: Boolean get()= statements.all { it.isNoop }

    override val modifiedContext: ExecutionScopedCTContext
        get() = statements.lastOrNull()?.modifiedContext ?: context

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        this.statements.forEach {
            it.setExpectedReturnType(type, diagnosis)
        }
    }

    override val isEvaluationResultReferenceCounted: Boolean
        get() = lastStatementAsExpression != null && lastStatementAsExpression.isEvaluationResultReferenceCounted

    override val isEvaluationResultAnchored: Boolean
        get() = lastStatementAsExpression == null || lastStatementAsExpression.isEvaluationResultAnchored

    private var expectedImplicitEvaluationResultType: BoundTypeReference? = null
    private var isInExpressionContext = false
    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        expectedImplicitEvaluationResultType = type
        isInExpressionContext = true
        lastStatementAsExpression?.setExpectedEvaluationResultType(type, diagnosis)
    }

    override fun markEvaluationResultUsed() {
        isInExpressionContext = true
        lastStatementAsExpression?.markEvaluationResultUsed()
    }

    private val seanHelper = SeanHelper()
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            statements.forEach { it.semanticAnalysisPhase1(diagnosis) }
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            statements.forEach { it.semanticAnalysisPhase2(diagnosis) }

            if (lastStatementAsExpression != null) {
                type = lastStatementAsExpression.type
            } else {
                val lastStatement = statements.lastOrNull()
                if (lastStatement?.modifiedContext?.getEphemeralState(CallFrameExit)?.isGuaranteedToReturnThrowOrTerminate == true) {
                    // implicit evaluation never matters
                    type = context.swCtx.getBottomType(lastStatement.declaration.span)
                } else if (isInExpressionContext) {
                    // the type is still unit, technically. However, this will trigger a confusing error message
                    // using the bottom type hides that error, and this becomes the more understandable alternative
                    diagnosis.implicitlyEvaluatingAStatement(statements.lastOrNull() ?: this)
                    type = context.swCtx.getBottomType(lastStatement?.declaration?.span ?: declaration.span)
                } else {
                    type = context.swCtx.unit.getBoundReferenceAssertNoTypeParameters(lastStatement?.declaration?.span ?: declaration.span)
                }
            }
        }
    }

    private var nothrowBoundary: NothrowViolationDiagnostic.SideEffectBoundary? = null
    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        seanHelper.requirePhase3NotDone()
        require(nothrowBoundary == null) { "setNothrow called more than once" }

        this.nothrowBoundary = boundary
        statements.forEach { it.setNothrow(boundary) }
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        lastStatementAsExpression?.setEvaluationResultUsage(valueUsage)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            statements.forEach { it.semanticAnalysisPhase3(diagnosis) }
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        seanHelper.requirePhase3Done()
        statements.forEach {
            handleCyclicInvocation(
                context = this,
                action = { it.visitReadsBeyond(boundary, visitor) },
                onCycle = { },
            )
        }
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        seanHelper.requirePhase3Done()
        statements.forEach {
            handleCyclicInvocation(
                context = this,
                action = { it.visitWritesBeyond(boundary, visitor) },
                onCycle = { },
            )
        }
    }

    private fun getDeferredCodeAtEndOfChunk(): List<IrExecutable> {
        return modifiedContext
            .getScopeLocalDeferredCode()
            .mapToBackendIrWithDebugLocations()
    }

    override fun toBackendIrStatement(): IrCodeChunk {
        return IrCodeChunkImpl(
            statements.mapToBackendIrWithDebugLocations() + getDeferredCodeAtEndOfChunk()
        )
    }

    override val isCompileTimeConstant: Boolean
        get() = lastStatementAsExpression != null && lastStatementAsExpression.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        return toBackendIrAsImplicitEvaluationExpression(isEvaluationResultReferenceCounted)
    }

    /**
     * @param assureResultHasReferenceCountIncrement if true and if the implicit result has
     * [BoundExpression.isEvaluationResultReferenceCounted] == `false`, will include an [IrCreateStrongReferenceStatement]
     * for the temporary implicit result.
     */
    fun toBackendIrAsImplicitEvaluationExpression(assureResultHasReferenceCountIncrement: Boolean): IrImplicitEvaluationExpressionImpl {
        val plainStatements = statements
            .take((statements.size - 1).coerceAtLeast(0))
            .mapToBackendIrWithDebugLocations()
            .toMutableList()

        val lastStatement = statements.lastOrNull()

        if (lastStatement is BoundExpression<*>) {
            plainStatements.add(IrUpdateSourceLocationStatementImpl(lastStatement.declaration.span))
            val implicitValueTemporary = IrCreateTemporaryValueImpl(
                lastStatement.toBackendIrExpression(),
                expectedImplicitEvaluationResultType?.toBackendIr(),
            )
            plainStatements += implicitValueTemporary
            if (lastStatement.isEvaluationResultReferenceCounted) {
                check(assureResultHasReferenceCountIncrement) {
                    "Reference counting bug: the implicit result is implicitly reference counted (${lastStatement::class.simpleName}) but the code using the result isn't aware."
                }
            } else if (assureResultHasReferenceCountIncrement) {
                plainStatements += IrCreateStrongReferenceStatementImpl(implicitValueTemporary)
            }
            return IrImplicitEvaluationExpressionImpl(
                IrCodeChunkImpl(plainStatements + getDeferredCodeAtEndOfChunk()),
                IrTemporaryValueReferenceImpl(implicitValueTemporary),
            )
        }

        val standInLiteralTemporary = IrCreateTemporaryValueImpl(
            IrStaticDispatchFunctionInvocationImpl(
                context.swCtx.unit.resolveMemberFunction("instance")
                    .single { it.parameterCount == 0 }
                    .overloads
                    .single()
                    .toBackendIr(),
                emptyList(),
                emptyMap(),
                context.swCtx.unit.irReadNotNullReference,
                null,
            )
        )
        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(plainStatements + listOfNotNull(lastStatement?.toBackendIrStatement()) + getDeferredCodeAtEndOfChunk() + listOf(standInLiteralTemporary)),
            IrTemporaryValueReferenceImpl(standInLiteralTemporary),
        )
    }

    companion object {
        fun fromBoundStatements(
            statements: List<BoundStatement<*>>,
            fallbackContext: ExecutionScopedCTContext,
        ): BoundCodeChunk {
            return BoundCodeChunk(
                statements.firstOrNull()?.context ?: fallbackContext,
                AstCodeChunk(statements.map { it.declaration }),
                statements,
            )
        }
    }
}