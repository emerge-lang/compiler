package compiler.binding

import compiler.InternalCompilerError
import compiler.ast.Statement
import compiler.ast.VariableDeclaration
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.expression.IrVariableAccessExpressionImpl
import compiler.binding.misc_ir.IrCreateTemporaryValueImpl
import compiler.binding.misc_ir.IrDropStrongReferenceStatementImpl
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrExecutable

class DropLocalVariableStatement(
    val variable: BoundVariable,
) : Statement {
    override val span = variable.declaration.span
    override fun bindTo(contextOnDeferredExecution: ExecutionScopedCTContext) = object : BoundStatement<VariableDeclaration> {
        override val context = contextOnDeferredExecution
        override val declaration = variable.declaration
        override val returnBehavior = SideEffectPrediction.NEVER
        override val throwBehavior: SideEffectPrediction? get() {
            val type = variable.typeAtDeclarationTime ?: return SideEffectPrediction.POSSIBLY
            val baseType = when {
                type is RootResolvedTypeReference -> type.baseType
                type is NullableTypeReference && type.nested is RootResolvedTypeReference -> type.nested.baseType
                else -> return SideEffectPrediction.POSSIBLY
            }
            if (baseType.kind != BoundBaseType.Kind.CLASS) return SideEffectPrediction.POSSIBLY
            return baseType.destructor?.throwBehavior
        }
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