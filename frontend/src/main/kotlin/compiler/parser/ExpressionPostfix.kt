package compiler.parser

import compiler.InternalCompilerError
import compiler.ast.AstSemanticOperator
import compiler.ast.Expression
import compiler.ast.expression.AstCastExpression
import compiler.ast.expression.AstIndexAccessExpression
import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.InvocationExpression
import compiler.ast.expression.MemberAccessExpression
import compiler.ast.expression.NotNullExpression
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
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
    val typeArguments: List<TypeArgument>?,
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
    val operator: KeywordToken,
    val toType: TypeReference,
) : ExpressionPostfix<AstCastExpression> {
    override fun modify(expr: Expression) = AstCastExpression(expr, operator, toType)
}

class BinaryExpressionPostfix(
    val operatorsOrExpressions: List<OperatorOrExpression>,
) : ExpressionPostfix<Expression> {
    override fun modify(expr: Expression): Expression {
        return buildBinaryExpressionAst(listOf(expr) + operatorsOrExpressions)
    }
}

private typealias OperatorOrExpression = Any // kotlin does not have a union type; if it had, this would be = AstSemanticOperator | Expression

/**
 * Operator priority/precedence. The higher the priority, the more aggressively the operator
 * binds to terms around it. `*` and `/` have a higher priority than `+` or `-`, as per
 * the rules of mathematics.
 */
private val AstSemanticOperator.priority: Int
    get() = when(operatorElement) {
        Operator.ELVIS -> 10

        Operator.LESS_THAN,
        Operator.LESS_THAN_OR_EQUALS,
        Operator.GREATER_THAN,
        Operator.GREATER_THAN_OR_EQUALS,
        Operator.EQUALS,
        Operator.NOT_EQUALS,
        Operator.IDENTITY_EQ,
        Operator.IDENTITY_NEQ -> 20

        Operator.PLUS,
        Operator.MINUS -> 30

        Operator.TIMES,
        Operator.DIVIDE -> 40
        else -> throw InternalCompilerError("$this is not a binary operator")
    }

/**
 * Takes as input a list of alternating [Expression]s and [OperatorToken]s, e.g.:
 *     [Identifier(a), Operator(+), Identifier(b), Operator(*), Identifier(c)]
 * Builds the AST with respect to operator precedence defined in [Operator.priority]
 *
 * **Operator Precedence**
 *
 * Consider this input: `a * (b + c) + e * f + g`
 * Of those operators with the lowest precedence the rightmost will form the toplevel expression (the one
 * returned from this function). In this case it's the second `+`:
 *
 *                                   +
 *                                  / \
 *      [a, *, (b + c), +, e, *, f]    g
 *
 * This process is then recursively repeated for both sides of the node:
 *
 *                        +
 *                       / \
 *                      +   g
 *                     / \
 *     [a, *, (b + c)]    [e, *, f]
 *
 *     ---
 *               +
 *              / \
 *             +   g
 *            / \
 *           /   *
 *          /   / \
 *         *   e   f
 *        / \
 *       a  (b + c)
 */
private fun buildBinaryExpressionAst(rawExpression: List<OperatorOrExpression>): Expression {
    if (rawExpression.size == 1) {
        return rawExpression[0] as? Expression
            ?: throw InternalCompilerError("List with one item that is not an expression.. bug!")
    }

    @Suppress("UNCHECKED_CAST") // the type check is in the filter {}
    val operatorsWithIndex = rawExpression
        .mapIndexed { index, item -> Pair(index, item) }
        .filter { it.second is AstSemanticOperator } as List<Pair<Int, AstSemanticOperator>>

    val rightmostWithLeastPriority = operatorsWithIndex
        .reversed()
        .minByOrNull { it.second.priority }
        ?: throw InternalCompilerError("No operator in the list... how can this even be?")

    val leftOfOperator = rawExpression.subList(0, rightmostWithLeastPriority.first)
    val rightOfOperator = rawExpression.subList(rightmostWithLeastPriority.first + 1, rawExpression.size)

    return BinaryExpression(
        leftHandSide = buildBinaryExpressionAst(leftOfOperator),
        operator = rightmostWithLeastPriority.second,
        rightHandSide = buildBinaryExpressionAst(rightOfOperator)
    )
}