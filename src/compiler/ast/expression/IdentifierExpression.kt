package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.binding.expression.BoundIdentifierExpression
import compiler.lexer.IdentifierToken

/**
 * A expression that evaluates using an identigier (variable reference, type reference)
 *
 * The [bindTo] method on this class assumes that the identifier references a variable. If the
 * identifier expression is used within a context where it may denote something else that logic is handled by the
 * enclosing context. Some examples:
 * * within a method invocation: [InvocationExpression] may read the [identifier] and treat it as a method name
 * * within a constructor invocation: [InvocationExpression] may read the [identifier] and treat it as a type name
 */
class IdentifierExpression(val identifier: IdentifierToken) : Expression<BoundIdentifierExpression> {
    override val sourceLocation = identifier.sourceLocation

    override fun bindTo(context: CTContext): BoundIdentifierExpression {
        return BoundIdentifierExpression(context, this)
    }
}