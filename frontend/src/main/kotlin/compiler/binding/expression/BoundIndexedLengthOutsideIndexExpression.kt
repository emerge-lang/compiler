package compiler.binding.expression

import compiler.InternalCompilerError
import compiler.ast.expression.AstIndexedLengthExpression
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.impurity.ImpurityVisitor
import compiler.binding.type.BoundTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.IndexedLengthOutsideIndexDiagnostic
import compiler.diagnostic.NothrowViolationDiagnostic
import io.github.tmarsteel.emerge.backend.api.ir.IrExpression

class BoundIndexedLengthOutsideIndexExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstIndexedLengthExpression,
) : BoundExpression<AstIndexedLengthExpression> {
    override val type: BoundTypeReference get() = context.swCtx.uword.getBoundReferenceAssertNoTypeParameters(declaration.span)
    override val modifiedContext get() = context

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        diagnosis.add(IndexedLengthOutsideIndexDiagnostic(declaration))
    }

    override fun setExpectedEvaluationResultType(type: BoundTypeReference, diagnosis: Diagnosis) = Unit
    override fun setEvaluationResultUsage(valueUsage: ValueUsage) = Unit
    override fun setNothrow(boundary: NothrowViolationDiagnostic.SideEffectBoundary) = Unit
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) = Unit
    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) = Unit
    override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
    override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit

    override val isEvaluationResultReferenceCounted = false
    override val isEvaluationResultAnchored = true
    override val isCompileTimeConstant = false

    override fun toBackendIrExpression(): IrExpression {
        throw InternalCompilerError("$ outside of an index access should have been reported as an error")
    }
}
