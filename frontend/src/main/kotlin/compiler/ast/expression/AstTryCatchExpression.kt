package compiler.ast.expression

import compiler.ast.AstCodeChunk
import compiler.ast.Executable
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.binding.context.TryBlockExecutionScopedCTContext
import compiler.binding.expression.BoundExpression
import compiler.binding.expression.BoundTryCatchExpression
import compiler.lexer.Span
import compiler.ast.Expression as AstExpression
import compiler.ast.Statement as AstStatement

class AstTryCatchExpression(
    override val span: Span,
    val fallibleCode: Executable,
    val catchBlock: AstCatchBlockExpression,
) : AstExpression {
    override fun bindTo(context: ExecutionScopedCTContext): BoundExpression<*> {
        val fallibleCodeAsChunk = when(fallibleCode) {
            is AstCodeChunk -> fallibleCode
            is AstStatement -> AstCodeChunk(listOf(fallibleCode))
        }
        val boundFallibleCode = fallibleCodeAsChunk.bindTo(
            TryBlockExecutionScopedCTContext(context)
        )

        return BoundTryCatchExpression(
            context,
            this,
            boundFallibleCode,
            catchBlock.bindTo(MutableExecutionScopedCTContext.deriveNewScopeFrom(context, ExecutionScopedCTContext.Repetition.MAYBE)),
        )
    }
}