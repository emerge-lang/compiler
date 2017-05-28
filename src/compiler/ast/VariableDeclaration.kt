package compiler.ast

import compiler.ast.expression.Expression
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.binding.BoundVariable
import compiler.binding.context.CTContext
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

open class VariableDeclaration(
    override val declaredAt: SourceLocation,
    val typeModifier: TypeModifier?,
    val name: IdentifierToken,
    val type: TypeReference?,
    val isAssignable: Boolean,
    val initializerExpression: Expression<*>?
) : Declaration, Executable<BoundVariable> {
    override val sourceLocation = declaredAt

    override fun bindTo(context: CTContext): BoundVariable = BoundVariable(context, this, initializerExpression?.bindTo(context))
}