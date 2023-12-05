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
import compiler.binding.type.ResolvedTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.UnresolvedType
import compiler.lexer.IdentifierToken

open class TypeReference(
    val simpleName: String,
    val nullability: Nullability = Nullability.UNSPECIFIED,
    open val modifier: TypeModifier? = null,
    val variance: Variance = Variance.UNSPECIFIED,
    val declaringNameToken: IdentifierToken? = null,
    val parameters: List<TypeReference> = emptyList(),
) {
    constructor(simpleName: IdentifierToken) : this(simpleName.value, declaringNameToken = simpleName)

    open fun modifiedWith(modifier: TypeModifier): TypeReference {
        // TODO: implement type modifiers
        return TypeReference(
            simpleName,
            nullability,
            modifier,
            variance,
            declaringNameToken,
            parameters,
        )
    }

    fun withVariance(variance: Variance): TypeReference {
        check(this.variance == Variance.UNSPECIFIED)
        return TypeReference(
            simpleName,
            nullability,
            modifier,
            variance,
            declaringNameToken,
            parameters,
        )
    }

    open fun resolveWithin(context: CTContext): ResolvedTypeReference {
        val resolvedParameters = parameters.map { it.resolveWithin(context).defaultMutabilityTo(modifier) }
        return context.resolveType(this)
            ?.let { RootResolvedTypeReference(this, context, it, resolvedParameters) }
            ?: UnresolvedType(context, this, resolvedParameters)
    }

    private lateinit var _string: String
    override fun toString(): String {
        if (!this::_string.isInitialized) {
            val buffer = StringBuilder()

            if (variance != Variance.UNSPECIFIED) {
                buffer.append(variance.name.lowercase())
                buffer.append(' ')
            }

            modifier?.let {
                buffer.append(it.name.lowercase())
                buffer.append(' ')
            }

            if (declaringNameToken != null) {
                buffer.append(declaringNameToken.value)
            } else {
                buffer.append(simpleName)
            }

            if (parameters.isNotEmpty()) {
                buffer.append(parameters.joinToString(
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

    enum class Nullability {
        UNSPECIFIED,
        NULLABLE,
        NOT_NULLABLE,
    }

    enum class Variance {
        UNSPECIFIED,
        IN,
        OUT
    }
}