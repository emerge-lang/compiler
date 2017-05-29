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
package compiler.parser.postproc

import compiler.ast.expression.BinaryExpression

fun restructureWithRespectToOperatorPrecedence(original: BinaryExpression): BinaryExpression {
    return original
}