package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.Expression
import compiler.lexer.Operator
import compiler.lexer.OperatorToken

/**
 * Restructures [BinaryExpression]s so that the resulting tree structure complies to the operator precedence. This is
 * the algorithm used:
 *
 * Given the source code `a * b + c` the following tree structure will result:
 *
 *       *
 *      / \
 *     a   +
 *        / \
 *       b   c
 *
 * Which would eventually evaluate as `a * (b + c)` which is obviously not correct.
 *
 * To solve this issue, the tree is flattened out into a sequence of [Expression]s and [Operator]s. The flattening
 * is recursive through [BinaryExpression]s but takes every other kind of [Expression] as-is. For example:
 *
 *        *
 *       / \
 *      a   +      => becomes => [a, *, b, +, c]
 *         / \
 *        b   c
 *
 *  and `a * (b + c) + e * f` which parses to
 *
 *              *
 *             / \
 *            a   +
 *              /   \         => becomes => [a, *, (b + c), +, e, *, f]
 *            ()     *
 *            |     / \
 *            +    e   f
 *          /  \
 *         b    c
 *
 *  The `(b + c)` part stays at it is. It should already have been restructured by another invocation of this method.
 *
 *  The resulting list is then used to build another tree:
 *  Of those operators with the lowest precedence the leftmost will from the toplevel node/expression. In this case
 *  it's the first and only `+`:
 *
 *                       +
 *                      / \
 *      [a, *, (b + c)]    [e, *, f]
 *
 *  This process is then recursively repeated for both sides of the node:
 *
 *              +
 *            /  \
 *           /    *
 *          /    / \
 *         *    e   f
 *       /  \
 *      a  (b + c)
 *
 * This tree then evaluates as desired: `(a * (b + c)) + (e * f) = a * (b + c) + e * f`.
 */
fun restructureWithRespectToOperatorPrecedence(original: BinaryExpression) = rearrange(original.flattened)

private typealias OperatorOrExpression = Any // kotlin does not have a union type; if it hat, this would be = Operator | Expression

/**
 * Flattens an expression
 */
private val Expression<*>.flattened: List<OperatorOrExpression>
    get() = when(this) {
        is BinaryExpression -> leftHandSide.flattened + listOf(op) + rightHandSide.flattened
        else -> listOf(this)
    }

/**
 * Does the rearranging part: takes the flattened expression and builds a tree recursively, taking
 * into account the operators [priority]
 */
private fun rearrange(items: List<OperatorOrExpression>): Expression<*> {
    if (items.size == 0) throw InternalCompilerError("Empty item list ... something went wrong!")

    if (items.size == 1) {
        return items[0] as? Expression<*> ?: throw InternalCompilerError("List with single item that is not an expression... ooops?")
    }

    val operatorsWithIndex = items
        .mapIndexed { index, item -> Pair(index, item) }
        .filter { it.second is OperatorToken } as List<Pair<Int, OperatorToken>>

    val leftmostWithLeastPriority = operatorsWithIndex
        .sortedBy { it.second.operator.priority }
        .firstOrNull() ?: throw InternalCompilerError("No operator in the list... how can this even be?")

    val leftOfOperator = items.subList(0, leftmostWithLeastPriority.first)
    val rightOfOperator = items.subList(leftmostWithLeastPriority.first + 1, items.size)

    return BinaryExpression(
        leftHandSide = rearrange(leftOfOperator),
        op = leftmostWithLeastPriority.second,
        rightHandSide = rearrange(rightOfOperator)
    )
}

private val Operator.priority: Int
    get() = when(this) {
        Operator.PLUS, Operator.MINUS   -> 1
        Operator.TIMES, Operator.DIVIDE -> 2
        Operator.POWER                  -> 3
        else -> throw InternalCompilerError("$this is not a binary operator")
    }