package compiler.ast.types

import compiler.ast.types.TypeModifier
import compiler.lexer.IdentifierToken

class TypeReference(
    val typeName: IdentifierToken,
    val isNullable: Boolean,
    val modifier: TypeModifier = TypeModifier.MUTABLE
) {
    fun modifiedWith(modifier: TypeModifier): TypeReference {
        // TODO: implement type modifiers
        return TypeReference(typeName, isNullable, modifier)
    }
}