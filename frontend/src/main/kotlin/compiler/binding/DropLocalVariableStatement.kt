package compiler.binding

import compiler.InternalCompilerError
import compiler.ast.Statement
import compiler.ast.VariableDeclaration
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.type.BoundTypeReference
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class DropLocalVariableStatement(
    val variable: BoundVariable,
) : Statement {
    override val span = variable.declaration.span
    override fun bindTo(contextOnDeferredExecution: ExecutionScopedCTContext) = object : BoundStatement<VariableDeclaration> {
        override val context = contextOnDeferredExecution
        override val declaration = variable.declaration
        override val isGuaranteedToThrow = false
        override val implicitEvaluationResultType = null

        override fun requireImplicitEvaluationTo(type: BoundTypeReference) {
            throw InternalCompilerError("Cannot have a deferred statement be an implicit evaluation result")
        }

        override fun toBackendIrStatement(): IrExecutable {
            val valueTemporary = IrCreateTemporaryValueImpl(IrVariableAccessExpressionImpl(variable.backendIrDeclaration))
            return IrCodeChunkImpl(listOf(
                valueTemporary,
                IrDropStrongReferenceStatementImpl(valueTemporary),
            ))
        }

        override fun semanticAnalysisPhase1(): Collection<Reporting> = emptyList()
        override fun semanticAnalysisPhase2(): Collection<Reporting> = emptyList()
        override fun semanticAnalysisPhase3(): Collection<Reporting> = emptyList()
    }
}