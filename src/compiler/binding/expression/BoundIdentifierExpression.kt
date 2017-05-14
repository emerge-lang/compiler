package compiler.binding.expression

import compiler.ast.expression.IdentifierExpression
import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference

class BoundIdentifierExpression(
    override val context: CTContext,
    override val declaration: IdentifierExpression
) : BoundExpression<IdentifierExpression> {
    val identifier: String = declaration.identifier.value

    override var type: BaseTypeReference? = null
        private set

    fun resolveAsVariable(): Collection<Error> {
        // TODO: implement
        return emptySet()
    }
}
