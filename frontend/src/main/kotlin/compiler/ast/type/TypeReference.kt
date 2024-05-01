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

import compiler.lexer.IdentifierToken
import compiler.lexer.Span

data class TypeReference(
    val simpleName: String,
    val nullability: Nullability = Nullability.UNSPECIFIED,
    val mutability: TypeMutability? = null,
    val declaringNameToken: IdentifierToken? = null,
    val arguments: List<TypeArgument>? = null,
) {
    constructor(simpleName: IdentifierToken) : this(simpleName.value, declaringNameToken = simpleName)

    val span: Span? = declaringNameToken?.span

    fun withMutability(mutability: TypeMutability): TypeReference {
        return TypeReference(
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
                Nullability.NOT_NULLABLE -> buffer.append('!')
                Nullability.NULLABLE -> buffer.append('?')
                Nullability.UNSPECIFIED -> {}
            }

            _string = buffer.toString()
        }

        return this._string
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as TypeReference

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

    enum class Nullability {
        UNSPECIFIED,
        NULLABLE,
        NOT_NULLABLE,
        ;
    }
}