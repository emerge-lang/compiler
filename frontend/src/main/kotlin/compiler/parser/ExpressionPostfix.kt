package compiler.parser

import compiler.InternalCompilerError
import compiler.ast.AstSemanticOperator
import compiler.ast.Expression
import compiler.ast.expression.AstCastExpression
import compiler.ast.expression.AstIndexAccessExpression
import compiler.ast.expression.AstInstanceOfExpression
import compiler.ast.expression.AstRangeExpression
import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.expression.NotNullExpression
import compiler.ast.expression.NumericLiteralExpression
import compiler.ast.expression.UnaryExpression
import compiler.ast.type.AstTypeArgument
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken

/**
 * Given the expression itself, it returns a new expression that contains the information about the postfix.
 * E.g. matching the !! postfix results in a [NotNullExpressionPostfix] which in turn will wrap any given
 * [Expression] in a [NotNullExpression].
 */
interface ExpressionPostfix<out OutExprType: Expression> {
    fun modify(expr: Expression): OutExprType
}

class NotNullExpressionPostfix(
    /** The notnull operator for reference; whether the operator is actually [Operator.NOTNULL] is never checked.*/
    val notNullOperator: OperatorToken
) : ExpressionPostfix<NotNullExpression> {
    override fun modify(expr: Expression) = NotNullExpression(expr, notNullOperator)
}

class InvocationExpressionPostfix(
    val typeArguments: List<AstTypeArgument>?,
    val valueParameterExpressions: List<Expression>,
    val closingParenthesis: OperatorToken,
) : ExpressionPostfix<InvocationExpression> {
    override fun modify(expr: Expression): InvocationExpression {
        val startLocation = when (expr) {
            is MemberAccessExpression -> expr.memberName.span
            else -> expr.span
        }
        val invocationLocation = startLocation .. closingParenthesis.span
        return InvocationExpression(expr, typeArguments, valueParameterExpressions, invocationLocation)
    }
}

class MemberAccessExpressionPostfix(
    /** must be either [Operator.DOT] or [Operator.SAFEDOT] */
    val accessOperatorToken: OperatorToken,
    val memberName: IdentifierToken
) : ExpressionPostfix<MemberAccessExpression> {
    override fun modify(expr: Expression) = MemberAccessExpression(expr, accessOperatorToken, memberName)
}

class IndexAccessExpressionPostfix(
    val sBraceOpen: OperatorToken,
    val indexExpr: Expression,
    val sBraceClose: OperatorToken,
) : ExpressionPostfix<AstIndexAccessExpression> {
    override fun modify(expr: Expression) = AstIndexAccessExpression(expr, sBraceOpen, indexExpr, sBraceClose)
}

class CastExpressionPostfix(
    val asToken: KeywordToken,
    val isSafe: Boolean,
    val toType: TypeReference,
) : ExpressionPostfix<AstCastExpression> {
    override fun modify(expr: Expression) = AstCastExpression(expr, asToken, isSafe, toType)
}

class InstanceOfExpressionPostfix(
    val operator: KeywordToken,
    val typeToCheck: TypeReference,
) : ExpressionPostfix<AstInstanceOfExpression> {
    override fun modify(expr: Expression): AstInstanceOfExpression {
        return AstInstanceOfExpression(expr, operator, typeToCheck)
    }
}


class PrefixedOperand(
    val prefixOperators: List<AstSemanticOperator>,
    val operand: Expression,
)

class OperatorExpressionBuilder private constructor(
    private val operands: List<PrefixedOperand>,
    private val infixOperators: List<AstSemanticOperator>,
) {
    private var operandIndex = 0
    private var prefixIndex = 0
    private var infixIndex = 0

    private fun parseExpression(enclosingOperator: AstSemanticOperator?, enclosingPower: Int): Expression {
        var expression = parseOperand(enclosingOperator, enclosingPower)
        while (infixIndex < infixOperators.size) {
            val operator = infixOperators[infixIndex]
            val power = operator.infixPower
            if (power <= enclosingPower) {
                break
            }
            infixIndex++
            val rightHandSide = parseExpression(operator, power)
            expression = if (operator.operatorElement == Operator.RANGE_UNTIL) {
                AstRangeExpression(expression, operator, rightHandSide)
            } else {
                BinaryExpression(expression, operator, rightHandSide)
            }
        }

        return expression
    }

    private fun parseOperand(enclosingOperator: AstSemanticOperator?, enclosingPower: Int): Expression {
        val unit = operands[operandIndex]
        if (prefixIndex < unit.prefixOperators.size) {
            val operator = unit.prefixOperators[prefixIndex++]
            val power = operator.prefixPower
            val valueExpression = parseExpression(operator, power)
            val weakerThanEnclosing = enclosingOperator?.takeIf { power < enclosingPower }
            if (operator.operatorElement == Operator.MINUS && valueExpression is NumericLiteralExpression && valueExpression.minusToken == null) {
                return NumericLiteralExpression(valueExpression.literalToken, operator.token as OperatorToken)
            }
            return UnaryExpression(operator, valueExpression, weakerThanEnclosing)
        }

        operandIndex++
        prefixIndex = 0
        return unit.operand
    }

    companion object {
        /**
         * Builds the AST of `operands[0] infixOperators[0] operands[1] infixOperators[1] ...` by precedence climbing,
         * using [infixPower] and [prefixPower]. All infix operators are left-associative.
         *
         * A prefix operator that binds weaker than the operator directly enclosing it (e.g. `a == not b`) still gets
         * its operand greedily, but the resulting [UnaryExpression] is marked so that semantic analysis reports it.
         * A unary minus directly applied to a numeric literal is folded into a negative literal, so that e.g. `-128`
         * fits `S8`.
         */
        fun buildOperatorExpression(operands: List<PrefixedOperand>, infixOperators: List<AstSemanticOperator>): Expression {
            require(operands.size == infixOperators.size + 1)
            return OperatorExpressionBuilder(operands, infixOperators).parseExpression(null, 0)
        }
    }
}

/**
 * Operator priority/precedence. The higher the priority, the more aggressively the operator
 * binds to terms around it. `*` and `/` have a higher priority than `+` or `-`, as per
 * the rules of mathematics.
 */
private val AstSemanticOperator.infixPower: Int
    get() = when(operatorElement) {
        Operator.NULL_COALESCE -> 10

        Keyword.OR -> 20
        Keyword.XOR -> 21
        Keyword.AND -> 22

        Operator.LESS_THAN,
        Operator.LESS_THAN_OR_EQUALS,
        Operator.GREATER_THAN,
        Operator.GREATER_THAN_OR_EQUALS,
        Operator.EQUALS,
        Operator.NOT_EQUALS -> 30

        Operator.RANGE_UNTIL -> 35

        Operator.PLUS,
        Operator.MINUS -> 40

        Operator.TIMES,
        Operator.DIVIDE -> 50
        else -> throw InternalCompilerError("$this is not a binary operator")
    }

/** Like [infixPower]; the operand of a prefix operator extends over all infix operators with a higher power. */
private val AstSemanticOperator.prefixPower: Int
    get() = when(operatorElement) {
        Keyword.NOT -> 25
        Operator.MINUS -> 60
        else -> throw InternalCompilerError("$this is not a prefix operator")
    }
