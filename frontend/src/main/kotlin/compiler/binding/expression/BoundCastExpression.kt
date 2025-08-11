package compiler.binding.expression

import compiler.InternalCompilerError
import compiler.ast.Expression
import compiler.ast.expression.AstCastExpression
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.IrCodeChunkImpl
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.effect.CallFrameExit
import compiler.binding.expression.BoundExpression.Companion.wrapIrAsStatement
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.IrSimpleTypeImpl
import compiler.binding.type.TypeUseSite
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.nothrowViolatingCast
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.api.ir.IrTypeMutability
import io.github.tmarsteel.emerge.common.EmergeConstants

/**
 * Currently this is merely a way to specify the type of numeric literals
 * For that use case it is supposed to stay long term; i think this is much cleaner than suffixes
 */
class BoundCastExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstCastExpression,
    val value: BoundExpression<*>,
    val safeCast: Boolean,
) : BoundExpression<Expression> by value {
    override val modifiedContext = if (safeCast) value.modifiedContext else {
        val newCtx = MutableExecutionScopedCTContext.deriveFrom(value.modifiedContext)
        newCtx.trackSideEffect(CallFrameExit.Effect.ThrowsPossibly)
        newCtx
    }

    override lateinit var type: BoundTypeReference
        private set

    private var baseTypeToCheck: BoundBaseType? = null
    private val isTypedNumericLiteral get() = value is BoundNumericLiteral

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {

        value.semanticAnalysisPhase1(diagnosis)

        val type = context.resolveType(declaration.toType)
        this.type = type
        if (safeCast) {
            this.type = this.type.withCombinedNullability(TypeReference.Nullability.NULLABLE)
        }
        type.validate(TypeUseSite.Irrelevant(declaration.span, null), diagnosis)
        baseTypeToCheck = validateTypeCheck(this, type, diagnosis)

        if (isTypedNumericLiteral) {
            // there is no suffix type notation for numeric literals; instead casting should do that
            // this enables the numeric literal to change its type based on what is required, e.g. 3 as U16
            value.setExpectedEvaluationResultType(type, diagnosis)
        }

        value.markEvaluationResultUsed()
    }

    override fun markEvaluationResultUsed() {
        // not forwarded as the cast uses the result of the value expression anyhow
    }

    private var expectedMutability: TypeMutability? = null
    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        // don't forward / isolate this from the to-be-cast expression
        expectedMutability = type.mutability
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        value.semanticAnalysisPhase2(diagnosis)
        val valueType = value.type
        val expectedMutability = this.expectedMutability
        if (valueType != null && declaration.toType.mutability == null && expectedMutability != null && valueType.mutability.isAssignableTo(expectedMutability)) {
            // user didn't specify mutability but the value fits what is expected in the context; allow this cross-talk across the cast boundary
            this.type = type.withMutability(expectedMutability)
        }
    }

    private var nothrowBoundary: NothrowViolationDiagnostic.SideEffectBoundary? = null
    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        nothrowBoundary = boundary
        value.setNothrow(boundary)
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        value.setEvaluationResultUsage(valueUsage.mapType { usedAsType ->
            if (type.mutability.isAssignableTo(usedAsType.mutability)) {
                usedAsType
            } else {
                usedAsType.withMutability(TypeMutability.READONLY)
            }
        })
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        value.setExpectedReturnType(type, diagnosis)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        value.semanticAnalysisPhase3(diagnosis)
        if (nothrowBoundary != null && !isTypedNumericLiteral) {
            diagnosis.nothrowViolatingCast(this, nothrowBoundary!!)
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        value.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        value.visitWritesBeyond(boundary, visitor)
    }

    override val isEvaluationResultReferenceCounted: Boolean get() = value.isEvaluationResultReferenceCounted
    override val isEvaluationResultAnchored: Boolean get() = value.isEvaluationResultAnchored
    override val isCompileTimeConstant: Boolean get() = value.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        if (isTypedNumericLiteral) {
            return value.toBackendIrExpression()
        }

        val irTargetType = type.toBackendIr()
        val valueToCastTemporary = IrCreateTemporaryValueImpl(value.toBackendIrExpression())
        val instanceOfResultTemporary = IrCreateTemporaryValueImpl(buildInstanceOf(context.swCtx, IrTemporaryValueReferenceImpl(valueToCastTemporary), baseTypeToCheck!!))

        if (safeCast) {
            val nullResultTemporary = IrCreateTemporaryValueImpl(IrNullLiteralExpressionImpl(irTargetType.asNullable()))
            val castOperationResultTemporary = IrCreateTemporaryValueImpl(IrIfExpressionImpl(
                condition = IrTemporaryValueReferenceImpl(instanceOfResultTemporary),
                thenBranch = IrImplicitEvaluationExpressionImpl(IrCodeChunkImpl(emptyList()), IrTemporaryValueReferenceImpl(valueToCastTemporary)),
                elseBranch = IrImplicitEvaluationExpressionImpl(
                    IrCodeChunkImpl(listOf(
                        nullResultTemporary
                    )),
                    IrTemporaryValueReferenceImpl(nullResultTemporary),
                ),
                irTargetType.asNullable(),
            ))
            return IrImplicitEvaluationExpressionImpl(
                IrCodeChunkImpl(listOf(
                    valueToCastTemporary,
                    instanceOfResultTemporary,
                    castOperationResultTemporary,
                )),
                IrTemporaryValueReferenceImpl(castOperationResultTemporary),
            )
        }

        val classCastErrorBoundType = context.swCtx
            .resolveBaseType(EmergeConstants.CoreModule.CAST_ERROR_TYPE_NAME)
            ?: throw InternalCompilerError("Could not resolve base type ${EmergeConstants.CoreModule.CAST_ERROR_TYPE_NAME}")

        val exceptionInstanceExpr = buildGenericInvocationLikeIr(
            context,
            declaration.span,
            emptyList(),
            { arguments, landingpad ->
                IrStaticDispatchFunctionInvocationImpl(
                    classCastErrorBoundType.constructor!!.toBackendIr(),
                    arguments,
                    emptyMap(),
                    IrSimpleTypeImpl(
                        classCastErrorBoundType.toBackendIr(),
                        IrTypeMutability.EXCLUSIVE,
                        isNullable = false,
                    ),
                    landingpad,
                )
            },
            assumeNothrow = false,
        )

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOf(
                valueToCastTemporary,
                instanceOfResultTemporary,
                IrConditionalBranchImpl(
                    condition = IrTemporaryValueReferenceImpl(instanceOfResultTemporary),
                    thenBranch = IrCodeChunkImpl(emptyList()),
                    elseBranch = buildIrThrow(
                        context,
                        exceptionInstanceExpr,
                        throwableInstanceIsReferenceCounted = true, // ctor invocation, is always counted
                        declaration.span,
                    ),
                ),
            )),
            object : IrTemporaryValueReference {
                override val declaration = valueToCastTemporary
                override val type: IrType get()= this@BoundCastExpression.type.toBackendIr()
            }
        )
    }

    override fun toBackendIrStatement(): IrExecutable {
        return this.wrapIrAsStatement()
    }
}