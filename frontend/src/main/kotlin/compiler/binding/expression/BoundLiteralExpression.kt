package compiler.binding.expression

import compiler.ast.Expression

/**
 * marker interface for literals
 */
interface BoundLiteralExpression<AstNode : Expression> : BoundExpression<AstNode> {
    override fun setEvaluationResultUsage(valueUsage: ValueUsage) {
        // for literals generally nothing to do
    }
}