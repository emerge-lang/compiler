package compiler.binding.expression

import compiler.ast.Expression
import compiler.ast.expression.AstIndexAccessExpression
import compiler.binding.context.ExecutionScopedCTContext

class BoundIndexAccessExpression(
    override val context: ExecutionScopedCTContext,
    override val declaration: AstIndexAccessExpression,
    private val hiddenInvocation: BoundInvocationExpression,
) : BoundExpression<Expression> by hiddenInvocation