package compiler.binding.expression

import compiler.ast.Expression

/**
 * marker interface for literals
 */
interface BoundLiteralExpression<AstNode : Expression> : BoundExpression<AstNode>