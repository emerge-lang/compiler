package compiler.binding.expression

import compiler.ast.expression.InvocationExpression
import compiler.binding.BoundExecutable
import compiler.binding.BoundFunction
import compiler.binding.context.CTContext

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
     * Receiver parameter of the function. This variable is `null` if the invoked function has no receiver
     * and the invocation was in a context without receiver.
     */
    val receiverValue: BoundExpression<*>?,

    /**
     * The values of the parameters, in order.
     */
    val parameterValues: List<BoundExpression<*>>
) : BoundInvocationExpression() {
    override val type = function?.returnType
}