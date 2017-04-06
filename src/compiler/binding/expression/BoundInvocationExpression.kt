package compiler.binding.expression

import compiler.ast.expression.InvocationExpression
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.BoundParameterList
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

abstract class BoundInvocationExpression : BoundExpression<InvocationExpression>, BoundExecutable<InvocationExpression>

/**
 * Statically dispatched invocation: the target jump address of the call is known at compile-time.
 *
 * Note that static dispatch can result from other kinds of invocation, too (e.g. dynamic dispatch where, at compile time,
 * it is known that the function is never overridden).
 */
class StaticDispatchInvocationExpression(
    override val context: CTContext,
    override val declaration: InvocationExpression,
    val functionName: String,

    /**
     * The invoked function. Is null if it could not be inferred.
     */
    val function: BoundFunction?,

    /**
     * Receiver parameter of the function. If the function has no receiver, [BoundNullLiteralExpression] is used.
     */
    val receiverValue: BoundExpression<*>,

    /**
     * The values of the parameters, in order.
     */
    val parameterValues: List<BoundExpression<*>>
) : BoundInvocationExpression() {
    override val type = function?.returnType
}