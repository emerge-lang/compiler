package compiler.ast.expression

import compiler.binding.BindingResult
import compiler.binding.context.CTContext
import compiler.binding.expression.BoundIdentifierExpression
import compiler.lexer.IdentifierToken
import compiler.parser.Reporting

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

    override fun bindTo(context: CTContext): BindingResult<BoundIdentifierExpression> {
        val variable = context.resolveVariable(identifier.value)

        return BindingResult(
            BoundIdentifierExpression(
                context,
                this,
                variable?.type
            ),
            if (variable == null) {
                // TODO refactor to an UndefinedVariableReporting
                setOf(Reporting.error("Unknown variable ${identifier.value}. TODO: Did you mean X, Y or Z?", identifier))
            }
            else {
                emptySet()
            }
        )
    }
}