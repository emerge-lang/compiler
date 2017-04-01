package compiler.binding.expression

import compiler.ast.expression.BinaryExpression
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.lexer.Operator

class BoundBinaryExpression(
    override val context: CTContext,
    override val declaration: BinaryExpression,
    override val type: BaseTypeReference?,
    val first: BoundExpression<*>,
    val operator: Operator,
    val second: BoundExpression<*>,
    val operatorFunction: BoundFunction?
) : BoundExpression<BinaryExpression>
