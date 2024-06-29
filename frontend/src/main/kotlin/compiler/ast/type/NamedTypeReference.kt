package compiler.ast.type

import compiler.lexer.IdentifierToken
import compiler.lexer.Span

data class NamedTypeReference(
    val simpleName: String,
    override val nullability: TypeReference.Nullability = TypeReference.Nullability.UNSPECIFIED,
    override val mutability: TypeMutability? = null,
    val declaringNameToken: IdentifierToken? = null,
    val arguments: List<TypeArgument>? = null,
) : TypeReference {
    constructor(simpleName: IdentifierToken) : this(simpleName.value, declaringNameToken = simpleName)

    override val span: Span? = declaringNameToken?.span

    override fun withMutability(mutability: TypeMutability): NamedTypeReference {
        return NamedTypeReference(
            simpleName,
            nullability,
            mutability,
            declaringNameToken,
            arguments,
        )
    }

    private lateinit var _string: String
    override fun toString(): String {
        if (!this::_string.isInitialized) {
            val buffer = StringBuilder()

            mutability?.let {
                buffer.append(it.name.lowercase())
                buffer.append(' ')
            }

            if (declaringNameToken != null) {
                buffer.append(declaringNameToken.value)
            } else {
                buffer.append(simpleName)
            }

            if (arguments != null) {
                buffer.append(arguments.joinToString(
                    prefix = "<",
                    separator = ", ",
                    postfix = ">"
                ))
            }

            when (nullability) {
                TypeReference.Nullability.NOT_NULLABLE -> buffer.append('!')
                TypeReference.Nullability.NULLABLE -> buffer.append('?')
                TypeReference.Nullability.UNSPECIFIED -> {}
            }

            _string = buffer.toString()
        }

        return this._string
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as NamedTypeReference

        if (simpleName != other.simpleName) return false
        if (nullability != other.nullability) return false
        if (mutability != other.mutability) return false
        if (arguments != other.arguments) return false

        return true
    }

    override fun hashCode(): Int {
        var result = simpleName.hashCode()
        result = 31 * result + nullability.hashCode()
        result = 31 * result + (mutability?.hashCode() ?: 0)
        result = 31 * result + arguments.hashCode()
        return result
    }
}