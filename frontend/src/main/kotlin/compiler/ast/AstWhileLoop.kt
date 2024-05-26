package compiler.ast

import compiler.binding.BoundCondition
import compiler.binding.BoundStatement
import compiler.binding.BoundWhileLoop
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.lexer.Span

class AstWhileLoop(
    override val span: Span,
    val condition: Expression,
    val body: CodeChunk,
) : Statement {
    override fun bindTo(context: ExecutionScopedCTContext): BoundStatement<*> {
        val conditionContext = MutableExecutionScopedCTContext.deriveFrom(context, ExecutionScopedCTContext.Repetition.ONCE_OR_MORE)
        val boundCondition = BoundCondition(condition.bindTo(conditionContext))
        val bodyContext = MutableExecutionScopedCTContext.deriveFrom(boundCondition.modifiedContext, ExecutionScopedCTContext.Repetition.ZERO_OR_MORE)
        val boundBody = body.bindTo(bodyContext)
        return BoundWhileLoop(
            context,
            this,
            boundCondition,
            boundBody,
        )
    }
}