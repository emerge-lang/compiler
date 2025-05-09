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
    val body: AstCodeChunk,
) : Statement {
    override fun bindTo(context: ExecutionScopedCTContext): BoundStatement<*> {
        lateinit var boundWhileHolder: BoundWhileLoop
        val conditionContext = MutableExecutionScopedCTContext.deriveNewLoopScopeFrom(context, true, { boundWhileHolder })
        val boundCondition = BoundCondition(conditionContext, condition.bindTo(conditionContext))
        val bodyContext = MutableExecutionScopedCTContext.deriveNewScopeFrom(boundCondition.modifiedContext, ExecutionScopedCTContext.Repetition.ZERO_OR_MORE)
        val boundBody = body.bindTo(bodyContext)
        boundWhileHolder = BoundWhileLoop(
            context,
            this,
            boundCondition,
            boundBody,
        )

        return boundWhileHolder
    }
}