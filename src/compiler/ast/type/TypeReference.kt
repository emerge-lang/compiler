package compiler.ast.type

import compiler.binding.context.CTContext
import compiler.binding.type.BaseTypeReference
import compiler.lexer.IdentifierToken

open class TypeReference(
    val declaredName: String,
    val isNullable: Boolean,
    open val modifier: TypeModifier? = null,
    val isInferred: Boolean = false,
    val declaringNameToken: IdentifierToken? = null
) {
    constructor(declaringNameToken: IdentifierToken, isNullable: Boolean, modifier: TypeModifier? = null, isInferred: Boolean = false)
        : this(declaringNameToken.value, isNullable, modifier, isInferred, declaringNameToken)

    open fun modifiedWith(modifier: TypeModifier): TypeReference {
        // TODO: implement type modifiers
        return TypeReference(declaredName, isNullable, modifier)
    }

    open fun nonNull(): TypeReference = TypeReference(declaredName, false, modifier, isInferred, declaringNameToken)

    open fun asInferred(): TypeReference = TypeReference(declaredName, isNullable, modifier, true, declaringNameToken)

    open fun resolveWithin(context: CTContext): BaseTypeReference? {
        val baseType = context.resolveAnyType(this)
        return if (baseType != null) BaseTypeReference(this, context, baseType) else null
    }
}