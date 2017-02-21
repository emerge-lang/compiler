package compiler.ast.type

import compiler.lexer.IdentifierToken

class TypeReference(
    val declaredName: String,
    val isNullable: Boolean,
    val modifier: TypeModifier = TypeModifier.MUTABLE,
    val isInferred: Boolean = false,
    val declaringNameToken: IdentifierToken? = null
) {
    constructor(declaringNameToken: IdentifierToken, isNullable: Boolean, modifier: TypeModifier = TypeModifier.MUTABLE, isInferred: Boolean = false)
        : this(declaringNameToken.value, isNullable, modifier, isInferred, declaringNameToken)

    fun modifiedWith(modifier: TypeModifier): TypeReference {
        // TODO: implement type modifiers
        return TypeReference(declaredName, isNullable, modifier)
    }

    fun asInferred(): TypeReference = TypeReference(declaredName, isNullable, modifier, true, declaringNameToken)
}