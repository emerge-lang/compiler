package compiler.binding

import compiler.ast.Statement
import compiler.ast.VariableDeclaration
import compiler.binding.context.CTContext
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.reportings.Diagnosis
import compiler.reportings.NothrowViolationReporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class DropLocalVariableStatement(
    val variable: BoundVariable,
) : Statement {
    override val span = variable.declaration.span
    override fun bindTo(contextOnDeferredExecution: ExecutionScopedCTContext) = object : BoundStatement<VariableDeclaration> {
        override val context = contextOnDeferredExecution
        override val declaration = variable.declaration
        override val returnBehavior = SideEffectPrediction.NEVER
        override val throwBehavior get() = SideEffectPrediction.NEVER

        override fun setNothrow(boundary: NothrowViolationReporting.SideEffectBoundary) {

        }

        override fun visitReadsBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
        override fun visitWritesBeyond(boundary: CTContext, visitor: ImpurityVisitor) = Unit
        override fun toBackendIrStatement(): IrExecutable {
            val valueTemporary = IrCreateTemporaryValueImpl(IrVariableAccessExpressionImpl(variable.backendIrDeclaration))
            return IrCodeChunkImpl(listOf(
                valueTemporary,
                IrDropStrongReferenceStatementImpl(valueTemporary),
            ))
        }

        override fun semanticAnalysisPhase1(diagnosis: Diagnosis) = Unit
        override fun semanticAnalysisPhase2(diagnosis: Diagnosis) = Unit
        override fun semanticAnalysisPhase3(diagnosis: Diagnosis) = Unit
    }
}