/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.ast.type

import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import compiler.lexer.Span
import io.github.tmarsteel.emerge.common.CanonicalElementName

/**
 * todo: rename to AstType
 */
sealed interface TypeReference {
    val span: Span?
    val nullability: Nullability
    val mutability: TypeMutability?

    /**
     * @return iff this reference is a placeholder asking for type inference, this method fills in the
     * referrable parts from [impliedType] and returns the resulting combination of information
     * from this instance and [impliedType].
     *
     * Otherwise, returns itself, resolved through [context]
     */
    fun resolveWithImpliedType(impliedType: RootResolvedTypeReference, context: CTContext): BoundTypeReference = context.resolveType(this)

    fun withMutability(mutability: TypeMutability): TypeReference

    fun withNullability(nullability: Nullability): TypeReference

    fun withSpan(span: Span): TypeReference

    fun intersect(other: TypeReference, span: Span = (this.span ?: Span.UNKNOWN) .. (other.span ?: Span.UNKNOWN)): AstIntersectionType

    enum class Nullability {
        UNSPECIFIED,
        NULLABLE,
        NOT_NULLABLE,
        ;

        /**
         * When intersecting two types, where one has `this` nullability and the other has [other] nullability,
         * the resulting type has the nullability as returned by this function.
         */
        fun intersect(other: Nullability): Nullability = when (this) {
            UNSPECIFIED -> other
            NULLABLE -> when (other) {
                UNSPECIFIED -> this
                NULLABLE -> NULLABLE
                NOT_NULLABLE -> NOT_NULLABLE
            }
            NOT_NULLABLE -> NOT_NULLABLE
        }

        companion object {
            fun of(type: BoundTypeReference): Nullability = if (type.isNullable) NULLABLE else NOT_NULLABLE
        }
    }
}

/**
 * Refers to a single [compiler.binding.basetype.BoundBaseType] / is not a compound type.
 */
sealed interface AstSimpleTypeReference : TypeReference {
    val simpleName: String
    val arguments: List<AstTypeArgument>?
    override fun withMutability(mutability: TypeMutability): AstSimpleTypeReference
    override fun withNullability(nullability: TypeReference.Nullability): AstSimpleTypeReference
}

/**
 * todo: rename to AstNamedType
 */
data class NamedTypeReference(
    override val simpleName: String,
    override val nullability: TypeReference.Nullability = TypeReference.Nullability.UNSPECIFIED,
    override val mutability: TypeMutability? = null,
    val declaringNameToken: IdentifierToken? = null,
    override val arguments: List<AstTypeArgument>? = null,
    override val span: Span? = declaringNameToken?.span,
) : AstSimpleTypeReference {
    constructor(simpleName: IdentifierToken) : this(simpleName.value, declaringNameToken = simpleName)

    override fun withMutability(mutability: TypeMutability): NamedTypeReference {
        return copy(mutability = mutability)
    }

    override fun withNullability(nullability: TypeReference.Nullability): NamedTypeReference {
        return copy(nullability = nullability)
    }

    override fun intersect(other: TypeReference, span: Span): AstIntersectionType = when(other) {
        is AstSimpleTypeReference -> AstIntersectionType(listOf(this, other), span)
        is AstIntersectionType -> AstIntersectionType(listOf(this) + other.components, span)
    }

    override fun withSpan(span: Span): TypeReference {
        return copy(span = span)
    }

    private lateinit var _string: String
    override fun toString(): String {
        if (!this::_string.isInitialized) {
            val buffer = StringBuilder()

            mutability?.let {
                buffer.append(it.toString())
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

    override fun resolveWithImpliedType(impliedType: RootResolvedTypeReference, context: CTContext): BoundTypeReference {
        if (this.simpleName != BoundTypeReference.NAME_REQUESTING_TYPE_INFERENCE) {
            return super.resolveWithImpliedType(impliedType, context)
        }

        if (arguments == null) {
            return impliedType
                .withCombinedNullability(this.nullability)
                .withMutability(this.mutability)
        }

        return context.resolveType(AstAbsoluteTypeReference(
            impliedType.baseType.canonicalName,
            arguments,
            this.nullability,
            this.mutability,
            this.span ?: Span.UNKNOWN,
        ))
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
        var result = javaClass.hashCode()
        result = 31 * result + simpleName.hashCode()
        result = 31 * result + nullability.hashCode()
        result = 31 * result + (mutability?.hashCode() ?: 0)
        result = 31 * result + arguments.hashCode()
        return result
    }
}

class AstIntersectionType(
    val components: List<AstSimpleTypeReference>,
    override val span: Span,
) : TypeReference {
    init {
        require(components.size > 1) {
            "intersection types with less than 2 components are nonsensical"
        }
    }

    override val nullability: TypeReference.Nullability by lazy {
        components.asSequence()
            .map { it.nullability }
            .reduce(TypeReference.Nullability::intersect)
    }

    override val mutability: TypeMutability? by lazy {
        components.asSequence()
            .map { it.mutability ?: TypeMutability.READONLY }
            .reduce(TypeMutability::intersect)
    }

    override fun withMutability(mutability: TypeMutability): AstIntersectionType {
        return AstIntersectionType(
            components.map { it.withMutability(mutability) },
            span,
        )
    }

    override fun withNullability(nullability: TypeReference.Nullability): TypeReference {
        if (this.nullability == nullability) {
            return this
        }

        return AstIntersectionType(
            components.map { it.withNullability(nullability) },
            span,
        )
    }

    override fun intersect(other: TypeReference, span: Span): AstIntersectionType = when(other) {
        is AstSimpleTypeReference -> AstIntersectionType(components + listOf(other), span)
        is AstIntersectionType -> AstIntersectionType(components + other.components, span)
    }

    override fun withSpan(span: Span) = AstIntersectionType(components, span)

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is AstIntersectionType) return false

        return components == other.components
    }

    override fun hashCode(): Int {
        var result = javaClass.hashCode()
        result = 31 * result + components.hashCode()

        return result
    }

    override fun toString() = components.joinToString(
        separator = " ${Operator.INTERSECTION.text} ",
    )
}

data class AstAbsoluteTypeReference(
    val canonicalTypeName: CanonicalElementName.BaseType,
    override val arguments: List<AstTypeArgument>? = null,
    override val nullability: TypeReference.Nullability = TypeReference.Nullability.UNSPECIFIED,
    override val mutability: TypeMutability? = null,
    override val span: Span,
) : AstSimpleTypeReference {
    override val simpleName = canonicalTypeName.simpleName

    override fun withMutability(mutability: TypeMutability): AstAbsoluteTypeReference {
        if (mutability == this.mutability) {
            return this
        }

        return copy(mutability = mutability)
    }

    override fun withNullability(nullability: TypeReference.Nullability): AstAbsoluteTypeReference {
        if (nullability == this.nullability) {
            return this
        }

        return copy(nullability = nullability)
    }

    override fun withSpan(span: Span): AstAbsoluteTypeReference {
        return copy(span = span)
    }

    override fun intersect(other: TypeReference, span: Span): AstIntersectionType {
        return when (other) {
            is AstIntersectionType -> AstIntersectionType(listOf(this) + other.components, span)
            is AstSimpleTypeReference -> return AstIntersectionType(listOf(this, other), span)
        }
    }
}