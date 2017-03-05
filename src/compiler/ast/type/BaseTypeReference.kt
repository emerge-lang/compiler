package compiler.ast.type

import compiler.ast.context.CTContext

/**
 * A [TypeReference] with resolved [BaseType]
 */
class BaseTypeReference(
    val original: TypeReference,
    val context: CTContext,
    val baseType: BaseType
) : TypeReference(
    original.declaredName,
    original.isNullable,
    original.modifier,
    original.isInferred,
    original.declaringNameToken
) {
    override fun modifiedWith(modifier: TypeModifier): BaseTypeReference {
        // TODO: implement type modifiers
        return BaseTypeReference(original.modifiedWith(modifier), context, baseType)
    }

    override fun nonNull(): BaseTypeReference = BaseTypeReference(original.nonNull(), context, baseType)

    override fun asInferred(): BaseTypeReference = BaseTypeReference(original.asInferred(), context, baseType)

    override fun toString() = "BaseType Ref[" + original.modifier + " " + baseType.fullyQualifiedName + "]"
}
