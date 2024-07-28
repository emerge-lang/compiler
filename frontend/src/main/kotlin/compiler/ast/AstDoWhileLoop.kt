package compiler.ast

import compiler.binding.BoundCondition
import compiler.binding.BoundDoWhileLoop
import compiler.binding.BoundStatement
import compiler.binding.context.ExecutionScopedCTContext
import compiler.binding.context.MutableExecutionScopedCTContext
import compiler.lexer.Span

class AstDoWhileLoop(
    override val span: Span,
    val condition: Expression,
    val body: AstCodeChunk,
) : Statement {
    override fun bindTo(context: ExecutionScopedCTContext): BoundStatement<*> {
        lateinit var boundLoopHolder: BoundDoWhileLoop
        val bodyContext = MutableExecutionScopedCTContext.deriveNewLoopScopeFrom(context, true, { boundLoopHolder })
        val boundBody = body.bindTo(bodyContext)
        val conditionContext = MutableExecutionScopedCTContext.deriveNewScopeFrom(boundBody.modifiedContext, ExecutionScopedCTContext.Repetition.ONCE_OR_MORE)
        val boundCondition = BoundCondition(condition.bindTo(conditionContext))
        boundLoopHolder = BoundDoWhileLoop(
            context,
            this,
            boundCondition,
            boundBody,
        )

        return boundLoopHolder
    }
}