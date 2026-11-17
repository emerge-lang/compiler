package compiler.binding.expression

import compiler.ast.expression.BinaryExpression
import compiler.binding.IrCodeChunkImpl
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.SingleBranchJoinExecutionScopedCTContext
import compiler.binding.context.effect.VariableTypeRefinement
import compiler.binding.impurity.Impurity
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrImplicitEvaluationExpressionImpl
import compiler.binding.misc_ir.IrTemporaryValueReferenceImpl
import compiler.binding.misc_ir.IrUpdateSourceLocationStatementImpl
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.NothrowViolationDiagnostic
import compiler.diagnostic.SideEffectInShortCircuitedOperandDiagnostic
import compiler.diagnostic.reportingShortCircuitedSideEffects
import compiler.lexer.Keyword
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

/**
 * `and` and `or`: the [rightHandSide] is only evaluated if the [leftHandSide] doesn't already decide the result.
 * Side effects in the [rightHandSide] are reported, as they happen only sometimes.
 */
class BoundShortCircuitExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: BinaryExpression,
    val operator: Operator,
    val leftHandSide: BoundExpression<*>,
    /** derived from [leftHandSide]'s [BoundExpression.modifiedContext] with [ExecutionScopedCTContext.Repetition.MAYBE] */
    private val contextForRightHandSide: MutableExecutionScopedCTContext,
    val rightHandSide: BoundExpression<*>,
) : BoundExpression<BinaryExpression> {
    enum class Operator(
        val keyword: Keyword,
        /** the result of the [leftHandSide] on which the [rightHandSide] is evaluated */
        val rightHandSideEvaluatedOn: BoundExpression.ImplyingResult,
        /** the result of the [leftHandSide] that decides the result alone */
        val shortCircuitsOn: BoundExpression.ImplyingResult,
        /** the result of the entire expression if the [rightHandSide] is not evaluated */
        val shortCircuitResult: Boolean,
    ) {
        AND(Keyword.AND, BoundExpression.ImplyingResult.BOOL_TRUE, BoundExpression.ImplyingResult.BOOL_FALSE, false),
        OR(Keyword.OR, BoundExpression.ImplyingResult.BOOL_FALSE, BoundExpression.ImplyingResult.BOOL_TRUE, true),
        ;
    }

    /**
     * Where the [leftHandSide] decided the result and the [rightHandSide] is not evaluated. Carries the implications of
     * that, for the code after where the [rightHandSide] doesn't complete normally (e.g. `isNull(v) or throw ...`).
     */
    private val contextWhenShortCircuited = MutableExecutionScopedCTContext.deriveFrom(leftHandSide.modifiedContext)

    override val modifiedContext: ExecutionScopedCTContext = SingleBranchJoinExecutionScopedCTContext(
        leftHandSide.modifiedContext,
        rightHandSide.modifiedContext,
        contextWhenShortCircuited,
    )

    override val type: BoundTypeReference by lazy {
        context.swCtx.bool.getBoundReferenceAssertNoTypeParameters(declaration.operator.token.span)
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        leftHandSide.semanticAnalysisPhase1(diagnosis)
        rightHandSide.semanticAnalysisPhase1(diagnosis)
        leftHandSide.markEvaluationResultUsed()
        rightHandSide.markEvaluationResultUsed()
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) {
        // the result is always Bool, nothing to infer from that
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        leftHandSide.setExpectedEvaluationResultType(type, diagnosis)
        rightHandSide.setExpectedEvaluationResultType(type, diagnosis)

        leftHandSide.semanticAnalysisPhase2(diagnosis)
        requireBoolOperand(leftHandSide, diagnosis)

        val lhsImplications = leftHandSide.implications
        VariableTypeRefinement.trackImplications(lhsImplications, operator.rightHandSideEvaluatedOn, contextForRightHandSide)
        VariableTypeRefinement.trackImplications(lhsImplications, operator.shortCircuitsOn, contextWhenShortCircuited)

        rightHandSide.semanticAnalysisPhase2(diagnosis)
        requireBoolOperand(rightHandSide, diagnosis)

        leftHandSide.setEvaluationResultUsage(IrrelevantValueUsage)
        rightHandSide.setEvaluationResultUsage(IrrelevantValueUsage)
    }

    private fun requireBoolOperand(operand: BoundExpression<*>, diagnosis: Diagnosis) {
        operand.type
            ?.evaluateAssignabilityTo(type, operand.declaration.span)
            ?.let(diagnosis::add)
    }

    /**
     * For `and`: if the result is true, both operands were evaluated and are true. For `or`: if the result is false,
     * both operands were evaluated and are false. The other result can come from either operand, so it implies
     * nothing.
     */
    override val implications: List<BoundExpression.ResultImplication> get() {
        return (leftHandSide.implications + rightHandSide.implications)
            .filter { it.onResult == operator.rightHandSideEvaluatedOn }
    }

    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        // the result is a new Bool value, usage is irrelevant
    }

    override fun setExpectedReturnType(type: BoundTypeReference, diagnosis: Diagnosis) {
        leftHandSide.setExpectedReturnType(type, diagnosis)
        rightHandSide.setExpectedReturnType(type, diagnosis)
    }

    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) {
        leftHandSide.setNothrow(boundary)
        rightHandSide.setNothrow(boundary)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        leftHandSide.semanticAnalysisPhase3(diagnosis)
        val alreadyReported = diagnosis.reportingShortCircuitedSideEffects(rightHandSide::semanticAnalysisPhase3)

        // the leftHandSide is always evaluated, so its side effects don't depend on anything
        rightHandSide.visitWritesBeyond(contextForRightHandSide) { impurity ->
            if (impurity.kind == Impurity.ActionKind.READ || impurity.span in alreadyReported) {
                return@visitWritesBeyond
            }
            diagnosis.add(SideEffectInShortCircuitedOperandDiagnostic(impurity, operator.keyword))
        }
    }

    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        leftHandSide.visitReadsBeyond(boundary, visitor)
        rightHandSide.visitReadsBeyond(boundary, visitor)
    }

    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) {
        leftHandSide.visitWritesBeyond(boundary, visitor)
        rightHandSide.visitWritesBeyond(boundary, visitor)
    }

    override val isEvaluationResultReferenceCounted = false
    override val isEvaluationResultAnchored = true
    override val isCompileTimeConstant: Boolean
        get() = leftHandSide.isCompileTimeConstant && rightHandSide.isCompileTimeConstant

    override fun toBackendIrExpression(): IrExpression {
        val irBool = type.toBackendIr()
        val lhsTemporary = IrCreateTemporaryValueImpl(leftHandSide.toBackendIrExpression())

        val rhsTemporary = IrCreateTemporaryValueImpl(rightHandSide.toBackendIrExpression())
        val evaluateRightHandSide = IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOf(
                IrUpdateSourceLocationStatementImpl(rightHandSide.declaration.span),
                rhsTemporary,
            )),
            IrTemporaryValueReferenceImpl(rhsTemporary),
        )

        val shortCircuitResultTemporary = IrCreateTemporaryValueImpl(IrBooleanLiteralExpressionImpl(irBool, operator.shortCircuitResult))
        val shortCircuit = IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOf(shortCircuitResultTemporary)),
            IrTemporaryValueReferenceImpl(shortCircuitResultTemporary),
        )

        val resultTemporary = IrCreateTemporaryValueImpl(IrIfExpressionImpl(
            IrTemporaryValueReferenceImpl(lhsTemporary),
            if (operator == Operator.AND) evaluateRightHandSide else shortCircuit,
            if (operator == Operator.AND) shortCircuit else evaluateRightHandSide,
            irBool,
        ))

        return IrImplicitEvaluationExpressionImpl(
            IrCodeChunkImpl(listOf(
                IrUpdateSourceLocationStatementImpl(leftHandSide.declaration.span),
                lhsTemporary,
                resultTemporary,
            )),
            IrTemporaryValueReferenceImpl(resultTemporary),
        )
    }
}
