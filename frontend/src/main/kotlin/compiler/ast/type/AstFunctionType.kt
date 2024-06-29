package compiler.ast.type

import compiler.ast.AstFunctionAttribute
import compiler.lexer.Span

data class AstFunctionType(
    override val span: Span,
    val attributes: List<AstFunctionAttribute>,
    val parameterTypes: List<TypeReference>,
    val returnType: TypeReference,
    override val nullability: TypeReference.Nullability,
) : TypeReference {
    /**
     * is always [TypeMutability.IMMUTABLE]:
     * functions cannot be mutated. They may read/write global or captured local state, but such behavior
     * is modeled through [AstFunctionAttribute.EffectCategory] in [attributes].
     */
    override val mutability: TypeMutability = TypeMutability.IMMUTABLE

    override fun withMutability(mutability: TypeMutability): AstFunctionType {
        return this
    }
}