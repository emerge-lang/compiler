package compiler.binding.expression

import compiler.ast.Expression
import compiler.binding.type.BoundTypeReference

/**
 * marker interface for literals
 */
interface BoundLiteralExpression<AstNode : Expression> : BoundExpression<AstNode> {
    override fun setUsageContext(usedAsType: BoundTypeReference) {
        // for literals generally nothing to do
    }
}