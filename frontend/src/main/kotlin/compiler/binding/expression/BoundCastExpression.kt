package compiler.binding.expression

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
import compiler.binding.context.effect.VariableTypeRefinement
import compiler.binding.expression.BoundExpression.Companion.tryAsVariable
import compiler.binding.expression.BoundExpression.Companion.wrapIrAsStatement
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.BoundIntersectionTypeReference
import compiler.binding.type.ErroneousType
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.StaticTypeCheckResult
import compiler.binding.type.TypeUseSite
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.TypeCheckKind
import compiler.diagnostic.forbiddenCast
import compiler.diagnostic.nothrowViolatingCast
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression
import io.github.tmarsteel.emerge.backend.api.ir.IrTemporaryValueReference
import io.github.tmarsteel.emerge.backend.api.ir.IrType

/**
 * `value as T` and `value as? T`: checks at runtime that the value is of the type, see [buildInstanceOf]; the
 * former throws `emerge.core.CastError` if it isn't, the latter evaluates to `null`.
 *
 * It also is the way to specify the type of numeric literals (`3 as U16`), where nothing is checked at runtime.
 * For that use case it is supposed to stay long term; i think this is much cleaner than suffixes
 */
class BoundCastExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstCastExpression,
    val value: BoundExpression<*>,
    val safeCast: Boolean,
) : BoundExpression<Expression> by value {
    /** the code after a strict cast only runs if the cast succeeded */
    private val contextAfterStrictCast: MutableExecutionScopedCTContext? = if (safeCast) null else {
        val newCtx = MutableExecutionScopedCTContext.deriveFrom(value.modifiedContext)
        newCtx.trackSideEffect(CallFrameExit.Effect.ThrowsPossibly)
        newCtx
    }
    override val modifiedContext: ExecutionScopedCTContext = contextAfterStrictCast ?: value.modifiedContext

    override lateinit var type: BoundTypeReference
        private set

    /** the type the value is checked against at runtime; for `as? T` that is `T`, though [type] is `T?` */
    private var typeToCheck: BoundTypeReference? = null
    private val isTypedNumericLiteral get() = value is BoundNumericLiteral

    /** the type as written after `as`; for `as? T` that is `T`, though [type] is `T?` */
    private lateinit var declaredTargetType: BoundTypeReference

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {

        value.semanticAnalysisPhase1(diagnosis)

        val type = context.resolveType(declaration.toType)
        this.type = type
        this.declaredTargetType = type
        if (safeCast) {
            this.type = this.type.withCombinedNullability(TypeReference.Nullability.NULLABLE)
        }
        type.validate(TypeUseSite.Irrelevant(declaration.span, null), diagnosis)
        typeToCheck = validateTypeCheck(type)

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
        var targetType = declaredTargetType
        if (valueType != null && declaration.toType.mutability == null && expectedMutability != null && valueType.mutability.isAssignableTo(expectedMutability)) {
            // user didn't specify mutability but the value fits what is expected in the context; allow this cross-talk across the cast boundary
            targetType = targetType.withMutability(expectedMutability)
        }

        if (valueType != null && !isTypedNumericLiteral && targetType !is ErroneousType && valueType !is ErroneousType) {
            val mutabilityIsFine = validateMutability(targetType, valueType, diagnosis)
            if (mutabilityIsFine) {
                staticResult = reportStaticResultOfTypeCheck(
                    if (safeCast) TypeCheckKind.SAFE_CAST else TypeCheckKind.CAST,
                    valueType,
                    typeToCheck,
                    declaration.asToken.span..declaration.toType.span,
                    diagnosis,
                    reportAlwaysSucceeds = { typeOfValue, _ -> !isDisambiguation(typeOfValue) },
                )
            }
        }

        this.type = if (safeCast) targetType.withCombinedNullability(TypeReference.Nullability.NULLABLE) else targetType

        // a strict cast throws unless the value is of the type; so in the code after it, the variable is of that type
        val localTypeToCheck = typeToCheck
        val subject = value.tryAsVariable()
        if (contextAfterStrictCast != null && localTypeToCheck != null && localTypeToCheck !is ErroneousType && subject != null && VariableTypeRefinement.canBeRefined(subject)) {
            contextAfterStrictCast.trackSideEffect(VariableTypeRefinement.Effect.Refine(subject, localTypeToCheck, contextAfterStrictCast))
        }
    }

    /**
     * An object doesn't know the mutability of the references to it, so no check at runtime can make a `read`
     * reference a `mut` one. Of the value itself, a cast can only keep or weaken the mutability (`x: read Any`,
     * `x as read Foo`), not strengthen it (`x as mut Foo`), and `own` is never the target of a cast.
     *
     * This is checked here where the target says its mutability. Where it is a type parameter (`x as T`), the
     * mutability is that of the type argument, and the check at runtime compares it with the mutability of the
     * reference (see [buildInstanceOf]).
     *
     * The mutability in type arguments (`x as Array<mut Foo>`) is no concern of this: objects know their type
     * arguments, mutability included, and the check at runtime covers it.
     *
     * @param target the type as written in the cast, never nullable just for the cast being `as?`
     * @param source the type of the value being cast
     * @return whether the mutability is fine: nothing was reported
     */
    private fun validateMutability(target: BoundTypeReference, source: BoundTypeReference, diagnosis: Diagnosis): Boolean {
        if (target.isOfConstClass) {
            return true
        }

        val reportAt = declaration.toType.span ?: declaration.span
        if (target.mutability == TypeMutability.OWN) {
            diagnosis.forbiddenCast(this, "Cannot cast to an own type: a cast cannot tell whether there are other references to the value.", reportAt)
        } else if (!source.mutability.isAssignableTo(target.mutability)) {
            diagnosis.forbiddenCast(
                this,
                "Cannot cast a ${source.mutability.keyword.text} value to a ${target.mutability.keyword.text} type: an object doesn't know the mutability of the references to it, so a cast can only keep or weaken it.",
                reportAt,
            )
        } else {
            return true
        }

        return false
    }

    /**
     * A value of an intersection type can have a member from more than one of the components (`p: A & B`, `p.foo()`).
     * Casting it to one of them is how to say which is meant (`(p as A).foo()`); that always succeeds and still
     * is not superfluous.
     */
    private fun isDisambiguation(typeOfValue: BoundTypeReference): Boolean {
        val nonNullable = (typeOfValue as? NullableTypeReference)?.nested ?: typeOfValue
        return !safeCast && nonNullable is BoundIntersectionTypeReference
    }

    /**
     * What the static type of the value tells about the check already; is set during [semanticAnalysisPhase2].
     * Where it always succeeds, there is no check at runtime, and nothing that throws.
     */
    private var staticResult: StaticTypeCheckResult = StaticTypeCheckResult.Unknown

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
        if (nothrowBoundary != null && !isTypedNumericLiteral && !safeCast && staticResult != StaticTypeCheckResult.AlwaysSucceeds) {
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
        if (staticResult == StaticTypeCheckResult.AlwaysSucceeds) {
            return IrImplicitEvaluationExpressionImpl(
                IrCodeChunkImpl(listOf(valueToCastTemporary)),
                IrTemporaryValueReferenceImpl(valueToCastTemporary, irTargetType),
            )
        }

        val instanceOfResultTemporary = IrCreateTemporaryValueImpl(buildInstanceOf(context.swCtx, IrTemporaryValueReferenceImpl(valueToCastTemporary), typeToCheck!!, value.type))

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

        val exceptionInstanceExpr = buildCastError(
            context.swCtx,
            IrTemporaryValueReferenceImpl(valueToCastTemporary),
            typeToCheck!!,
            value.type,
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
                        throwableInstanceIsReferenceCounted = true, // the result of an invocation, is always counted
                        throwableIsStaticallyAnError = true, // a CastError
                        declaration.span,
                    ),
                ),
            )),
            IrTemporaryValueReferenceImpl(valueToCastTemporary, irTargetType),
        )
    }

    override fun toBackendIrStatement(): IrExecutable {
        return this.wrapIrAsStatement()
    }
}