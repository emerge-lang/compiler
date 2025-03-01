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
import compiler.PlatformModule
import compiler.ast.expression.NotNullExpression
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.ImpurityVisitor
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.SoftwareContext
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrExpressionSideEffectsStatementImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrIsNullExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrCodeChunk
import io.github.tmarsteel.emerge.backend.api.ir.IrCreateTemporaryValue
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

class BoundNotNullExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: NotNullExpression,
    val nullableExpression: BoundExpression<*>
) : BoundExpression<NotNullExpression>, BoundExecutable<NotNullExpression> {
    // TODO: reporting on superfluous notnull when nullableExpression.type.nullable == false
    // TODO: obtain type from nullableExpression and remove nullability from the type

    override var type: BoundTypeReference? = null
        private set

    override val throwBehavior get() = nullableExpression.throwBehavior
    override val returnBehavior get() = nullableExpression.returnBehavior

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        nullableExpression.semanticAnalysisPhase1(diagnosis)
    }

    private var expectedEvaluationResultType: BoundTypeReference? = null
    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        expectedEvaluationResultType = type

        nullableExpression.setExpectedEvaluationResultType(type.withCombinedNullability(TypeReference.Nullability.NULLABLE), diagnosis)
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        nullableExpression.markEvaluationResultUsed()
        nullableExpression.semanticAnalysisPhase2(diagnosis)
        type = nullableExpression.type?.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)
            ?: expectedEvaluationResultType
    }

    private var nothrowBoundary: NothrowViolationReporting.SideEffectBoundary? = null
    override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {
        this.nothrowBoundary = boundary
    }

    private var nonNullResultUsed = false
    override fun markEvaluationResultUsed() {
        nonNullResultUsed = true
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        // this expression duplicates the reference. That doesn't prove a capture, but it would easily allow for one,
        // so it has to be treated as such.
        // defaulting to readonly is okay because: that only happens if the nullableExpression couldn't determine its
        // result type. That in and of itself must produce an ERROR-level diagnostic, stopping compilation in any case.
        nullableExpression.markEvaluationResultCaptured(type?.mutability ?: TypeMutability.READONLY)

        nullableExpression.semanticAnalysisPhase3(diagnosis)
        nothrowBoundary?.let { nothrowBoundary ->
            diagnosis.add(Reporting.nothrowViolatingNotNullAssertion(this, nothrowBoundary))
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor, diagnosis: Diagnosis) {
        nullableExpression.visitReadsBeyond(boundary, visitor, diagnosis)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor, diagnosis: Diagnosis) {
        nullableExpression.visitWritesBeyond(boundary, visitor, diagnosis)
    }

    override val isEvaluationResultReferenceCounted get() = nullableExpression.isEvaluationResultReferenceCounted
    override val isEvaluationResultAnchored get() = nullableExpression.isEvaluationResultAnchored
    override val isCompileTimeConstant get() = nullableExpression.isCompileTimeConstant

    /**
     * @return the `emerge.core.panic(emerge.core.String)` function
     */
    private val panicFunction: BoundFunction by lazy {
        val corePackage = context.swCtx.getPackage(PlatformModule.NAME)
            ?: throw InternalCompilerError("Package ${PlatformModule.NAME} not known to the ${SoftwareContext::class.simpleName}!")

        corePackage
            .getTopLevelFunctionOverloadSetsBySimpleName("panic")
            .asSequence()
            .filter { it.parameterCount == 1 }
            .flatMap { it.overloads.asSequence() }
            .filter {
                val paramType = it.parameterTypes[0] ?: return@filter false
                if (paramType !is RootResolvedTypeReference) return@filter false
                paramType.baseType == context.swCtx.string
            }
            .singleOrNull() ?: throw InternalCompilerError("Could not find the panic(String) function")
    }

    /**
     * first: the code that does the null check and error raising, second: the value that was checked
     */
    private val backendIr: Pair<IrCodeChunk, IrCreateTemporaryValue> by lazy {
        val valueToCheck = IrCreateTemporaryValueImpl(nullableExpression.toBackendIrExpression())
        val nullCmpResult = IrCreateTemporaryValueImpl(
            IrIsNullExpressionImpl(
                IrTemporaryValueReferenceImpl(valueToCheck),
                context.swCtx,
            )
        )

        // TODO: improve the error message by quoting from the source? e.g. "myVar.foo().someField evaluated to null"
        val errorMessage = IrCreateTemporaryValueImpl(
            IrStringLiteralExpressionImpl(
                "failed not-null assertion in ${declaration.span.fileLineColumnText}".toByteArray(Charsets.UTF_8),
                context.swCtx.string.baseReference.toBackendIr(),
            )
        )
        val panicInvocation = IrCreateTemporaryValueImpl(IrStaticDispatchFunctionInvocationImpl(
            panicFunction.toBackendIr(),
            listOf(IrTemporaryValueReferenceImpl(errorMessage)),
            emptyMap(),
            panicFunction.returnType!!.toBackendIr(),
            null,
        ))

        val code = IrCodeChunkImpl(listOf(
            valueToCheck,
            nullCmpResult,
            IrExpressionSideEffectsStatementImpl(IrIfExpressionImpl(
                IrTemporaryValueReferenceImpl(nullCmpResult),
                IrImplicitEvaluationExpressionImpl(
                    IrCodeChunkImpl(listOf(
                        errorMessage,
                        panicInvocation,
                    )),
                    IrTemporaryValueReferenceImpl(panicInvocation),
                ),
                null,
                context.swCtx.unit.baseReference.toBackendIr(),
            ))
        ))

        Pair(code, valueToCheck)
    }

    override fun toBackendIrExpression(): IrExpression {
        return IrImplicitEvaluationExpressionImpl(backendIr.first, IrTemporaryValueReferenceImpl(backendIr.second))
    }

    override fun toBackendIrStatement(): IrExecutable {
        return backendIr.first
    }
}