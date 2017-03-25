package compiler.ast.expression

import compiler.binding.context.CTContext
import compiler.ast.type.BaseTypeReference
import compiler.lexer.IdentifierToken
import compiler.parser.Reporting

/**
 * A expression that evaluates using an identigier (variable reference, type reference)
 *
 * The [validate] and [determineType] methods on this class assume that the identifier references a variable. If the
 * identifier expression is used within a function invocation, the validation and function loookup should happen within
 * the appropriate instance of [InvocationExpression]
 */
class IdentifierExpression(val identifier: IdentifierToken) : Expression {
    override val sourceLocation = identifier.sourceLocation

    override fun determineType(context: CTContext): BaseTypeReference? {
        return context.resolveVariable(identifier.value)?.type?.resolveWithin(context)
    }

    override fun validate(context: CTContext): Collection<Reporting> {
        val variable = context.resolveVariable(identifier.value)

        if (variable == null) {
            return setOf(Reporting.error("Unknown variable ${identifier.value}. TODO: Did you mean X, Y or Z?", identifier))
        }
        else {
            return emptySet()
        }
    }
}