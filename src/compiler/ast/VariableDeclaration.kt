package compiler.ast

import compiler.ast.context.CTContext
import compiler.ast.expression.Expression
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.SourceLocation

class VariableDeclaration(
    override val declaredAt: SourceLocation,
    val typeModifier: TypeModifier?,
    val name: IdentifierToken,
    val type: TypeReference?,
    val isAssignable: Boolean,
    val assignExpression: Expression?
) : Declaration {
    /**
     * Determines and returns the type of the variable when initialized in the given context. If the type cannot
     * be determined due to semantic errors, the closest guess is returned, even Any if there is absolutely no clue.
     */
    fun determineType(context: CTContext): TypeReference {
        val baseType: TypeReference = type ?: assignExpression?.determineType(context) ?: compiler.ast.type.Any.reference

        return if (typeModifier == null) baseType else baseType.modifiedWith(typeModifier)
    }
}