package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.CodeChunk
import compiler.ast.Executable
import compiler.ast.expression.*
import compiler.binding.expression.BoundExpression
import compiler.lexer.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun ExpressionPostprocessor(rule: Rule<*>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult({ tokens ->
            var expression = tokens.next()!! as Expression<*>
            @Suppress("UNCHECKED_CAST")
            val postfixes = tokens.remainingToList() as List<ExpressionPostfixModifier<*>>

            for (postfixMod in postfixes) {
                expression = postfixMod.modify(expression)
            }

            expression
        })
}

fun LiteralExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult({ tokens ->
            val valueToken = tokens.next()!!

            if (valueToken is NumericLiteralToken) {
                NumericLiteralExpression(valueToken)
            }
            else {
                throw InternalCompilerError("Unsupported literal value $valueToken")
            }
        })
}

fun ValueExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult({  things ->
            val valueThing = things.next()!!

            if (valueThing is Expression<*>) {
                valueThing
            }
            else if (valueThing is IdentifierToken) {
                if (valueThing.value == "true" || valueThing.value == "false") {
                    BooleanLiteralExpression(valueThing.sourceLocation, valueThing.value == "true")
                } else {
                    IdentifierExpression(valueThing)
                }
            }
            else {
                throw InternalCompilerError("Unsupported value $valueThing")
            }
        })
}

fun ParanthesisedExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult({ input ->
            val parantOpen = input.next()!! as OperatorToken
            val nested     = input.next()!! as Expression<*>

            ParenthesisedExpression(nested, parantOpen.sourceLocation)
        })
}

fun BracedCodeOrSingleStatementPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Executable<*>> {
    return rule
        .flatten()
        .mapResult { input ->
            var next: Any? = input.next()

            if (next == OperatorToken(Operator.CBRACE_OPEN)) {
                next = input.next()
                if (next is CodeChunk) {
                    next
                }
                else if (next != OperatorToken(Operator.CBRACE_CLOSE)) {
                    throw InternalCompilerError("Unepxected $next, expecting code or ${Operator.CBRACE_CLOSE}")
                }
                else {
                    CodeChunk(emptyList())
                }
            }
            else if (next is Executable<*>) {
                next
            }
            else {
                throw InternalCompilerError("Unexpected $next, expecting ${Operator.CBRACE_OPEN} or executable")
            }
        }
}

fun IfExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<IfExpression> {
    return rule
        .flatten()
        .mapResult { input ->
            val ifKeyword = input.next() as KeywordToken

            val condition = input.next() as Expression<BoundExpression<Expression<*>>>
            val thenCode: Executable<*> = input.next() as Executable<*>
            val elseCode: Executable<*>?

            if (input.hasNext()) {
                // skip ELSE
                input.next()
                elseCode = input.next() as Executable<*>
            }
            else {
                elseCode = null
            }

            IfExpression(
                ifKeyword.sourceLocation,
                condition,
                thenCode,
                elseCode
            )
        }
}

fun BinaryExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {

    return rule
        .flatten()
        .mapResult { input -> toAST_BinaryExpression(input.remainingToList()) }
}

private typealias OperatorOrExpression = Any // kotlin does not have a union type; if it hat, this would be = OperatorToken | Expression<*>

private val Operator.priority: Int
    get() = when(this) {
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

        Operator.CAST,
        Operator.TRYCAST -> 60
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
private fun toAST_BinaryExpression(rawExpression: List<OperatorOrExpression>): Expression<*> {
    if (rawExpression.size == 1) {
        return rawExpression[0] as? Expression<*> ?: throw InternalCompilerError("List with one item that is not an expression.. bug!")
    }

    val operatorsWithIndex = rawExpression
        .mapIndexed { index, item -> Pair(index, item) }
        .filter { it.second is OperatorToken } as List<Pair<Int, OperatorToken>>

    val rightmostWithLeastPriority = operatorsWithIndex
        .reversed()
        .minBy { it.second.operator.priority }
        ?: throw InternalCompilerError("No operator in the list... how can this even be?")

    val leftOfOperator = rawExpression.subList(0, rightmostWithLeastPriority.first)
    val rightOfOperator = rawExpression.subList(rightmostWithLeastPriority.first + 1, rawExpression.size)

    return BinaryExpression(
        leftHandSide = toAST_BinaryExpression(leftOfOperator),
        op = rightmostWithLeastPriority.second,
        rightHandSide = toAST_BinaryExpression(rightOfOperator)
    )
}

fun UnaryExpressionPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<Expression<*>> {
    return rule
        .flatten()
        .mapResult({ input ->
            val operator = (input.next()!! as OperatorToken).operator
            val expression = input.next()!! as Expression<*>
            UnaryExpression(operator, expression)
        })
}

/**
 * A postfix modifier resembles an expression postfix. Given the expression itself, it returns a new
 * expression that contains the information about the postfix. E.g. matching the !! postfix results in a
 * [NotNullExpressionPostfixModifier] which in turn will wrap any given [Expression] in a [NotNullExpression].
 */
interface ExpressionPostfixModifier<out OutExprType: Expression<*>> {
    fun modify(expr: Expression<*>): OutExprType
}

class NotNullExpressionPostfixModifier(
    /** The notnull operator for reference; whether the operator is actually [Operator.NOTNULL] is never checked.*/
    val notNullOperator: OperatorToken
) : ExpressionPostfixModifier<NotNullExpression> {
    override fun modify(expr: Expression<*>) = NotNullExpression(expr, notNullOperator)
}

class InvocationExpressionPostfixModifier(
    val parameterExpressions: List<Expression<*>>
) : ExpressionPostfixModifier<InvocationExpression> {
    override fun modify(expr: Expression<*>) = InvocationExpression(expr, parameterExpressions)

    companion object {
        fun fromMatchedTokens(input: TransactionalSequence<Any, Position>): InvocationExpressionPostfixModifier {
            // skip PARANT_OPEN
            input.next()!! as OperatorToken

            val paramExpressions = mutableListOf<Expression<*>>()
            while (input.peek() is Expression<*>) {
                paramExpressions.add(input.next()!! as Expression<*>)

                // skip COMMA or PARANT_CLOSE
                input.next()!! as OperatorToken
            }

            return InvocationExpressionPostfixModifier(paramExpressions)
        }
    }
}

class MemberAccessExpressionPostfixModifier(
    /** must be either [Operator.DOT] or [Operator.SAFEDOT] */
    val accessOperatorToken: OperatorToken,
    val memberName: IdentifierToken
) : ExpressionPostfixModifier<MemberAccessExpression> {
    override fun modify(expr: Expression<*>) = MemberAccessExpression(expr, accessOperatorToken, memberName)
}