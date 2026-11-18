package compiler.binding.expression

import compiler.ast.AstWhenExpression
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.SoftwareContext
import compiler.binding.context.effect.CallFrameExit
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.misc_ir.IrUnreachableStatementImpl
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

/**
 * The `else` branch the compiler adds to a `when` with `is` branches that doesn't have one, see
 * [AstWhenExpression.bindTo]. Where the branches are exhaustive, this code is never reached; otherwise it does
 * nothing, just like an absent `else` branch.
 */
class BoundWhenExhaustivenessFallback(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstWhenExpression.ExhaustivenessFallback,
    private val exhaustiveness: WhenExhaustiveness,
) : BoundExpression<AstWhenExpression.ExhaustivenessFallback> {
    private val _modifiedContext = MutableExecutionScopedCTContext.deriveFrom(context)
    override val modifiedContext: ExecutionScopedCTContext = _modifiedContext

    /**
     * Always the bottom type, so that the type of the `when` is that of the other branches. Where the `when` is
     * not exhaustive, it is either not used as a value, it evaluates to `Unit`, or [BoundWhenExpression] reports
     * the missing branches.
     */
    override val type: BoundTypeReference = context.swCtx.getBottomType(declaration.span)

    private val isExhaustive: Boolean get() = exhaustiveness.result == WhenExhaustiveness.Result.Exhaustive

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) = Unit

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        if (isExhaustive) {
            _modifiedContext.trackSideEffect(CallFrameExit.Effect.InvokesFunction(CallFrameExit.FunctionBehavior(
                throws = CallFrameExit.Occurrence.NEVER,
                terminates = CallFrameExit.Occurrence.GUARANTEED,
            )))
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) = Unit

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) = Unit
    override fun setEvaluationResultUsage(valueUsage: ValueUsage) = Unit
    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) = Unit
    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit

    override val isEvaluationResultReferenceCounted = false
    override val isEvaluationResultAnchored = true
    override val isCompileTimeConstant = false

    private fun buildUnreachable() = IrUnreachableStatementImpl(
        "none of the branches of the `when` at ${declaration.span} matched, though they cover all subtypes known at compile time",
        // the compiler can prove it, but if the program state is corrupted (e.g. through FFI), a panic is much more helpful than UB
        isProvablyUnreachable = false,
    )

    override fun toBackendIrStatement(): IrExecutable {
        return IrCodeChunkImpl(listOfNotNull(
            buildUnreachable().takeIf { isExhaustive },
        ))
    }

    override fun toBackendIrExpression(): IrExpression {
        // the backend needs a value even if the code is never reached
        val unitTemporary = IrCreateTemporaryValueImpl(context.swCtx.buildUnitInstanceIr())
        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOfNotNull(
                buildUnreachable().takeIf { isExhaustive },
                unitTemporary,
            )),
            IrTemporaryValueReferenceImpl(unitTemporary),
        )
    }
}

internal fun SoftwareContext.buildUnitInstanceIr(): IrExpression = IrStaticDispatchFunctionInvocationImpl(
    unit.resolveMemberFunction("instance")
        .single { it.parameterCount == 0 }
        .overloads
        .single()
        .toBackendIr(),
    emptyList(),
    emptyMap(),
    unit.irReadNotNullReference,
    null,
)
