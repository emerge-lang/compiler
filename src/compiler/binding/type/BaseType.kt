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

package compiler.binding.type

import compiler.ast.FunctionDeclaration
import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.binding.BoundFunction
import compiler.binding.ObjectMember
import compiler.binding.context.CTContext
import kotlinext.get

/**
 * Base type are classes, interfaces, enums, built-in type
 */
interface BaseType {
    val simpleName: String
        get() = javaClass.simpleName

    // TODO: infer this from declaring module and simpleName
    val fullyQualifiedName: String
        get() = simpleName

    val baseReference: (CTContext) -> ResolvedTypeReference
        get() = { ctx ->
            // determine minimum bound for all type parameters
            RootResolvedTypeReference(ctx, this, false, null, parameters.map {
                BoundTypeArgument(
                    ctx,
                    TypeArgument(
                        it.variance,
                        TypeReference("_"),
                    ),
                    it.variance,
                    it.bound?.let(ctx::resolveType) ?: UnresolvedType.getTypeParameterDefaultBound(ctx)
                )
            })
        }

    val superTypes: Set<BaseType>
        get() = emptySet()

    val constructors: Set<BoundFunction>
        get() = emptySet()

    val parameters: List<TypeParameter>
        get() = emptyList()

    /**
     * If true, values of this type can by design not change. This is the case for primitives like booleans
     * and ints, but could also apply to classes and structs who are declared as "immutable".
     */
    val isAtomic: Boolean
        get() = false

    /** @return Whether this type is the same as or a subtype of the given type. */
    infix fun isSubtypeOf(other: BaseType): Boolean {
        if (other === this) return true
        if (other === BuiltinNothing) return false

        return superTypes.map { it.isSubtypeOf(other) }.fold(false, Boolean::or)
    }

    /** @return The member function overloads for the given name or an empty collection if no such member function is defined. */
    fun resolveMemberFunction(name: String): Collection<FunctionDeclaration> = emptySet()

    fun resolveMemberVariable(name: String): ObjectMember? = null

    companion object {
        /**
         * Suppose
         *
         *     class A
         *     class AB : A
         *     class ABC : AB
         *     class C
         *
         * then these are the closest common ancestors:
         *
         * | Types       | Closes common ancestor |
         * | ----------- | ---------------------- |
         * | A, AB       | A                      |
         * | AB, ABC     | AB                     |
         * | A, ABC      | A                      |
         * | C, A        | Any                    |
         * | AB, C       | Any                    |
         *
         * @return the most specific type that all the given types can be assigned to
         */
        fun closestCommonSupertypeOf(types: List<BaseType>): BaseType {
            if (types.isEmpty()) throw IllegalArgumentException("At least one type must be provided")

            val typesExcludingNothing = types.filter { it !== BuiltinNothing }
            if (typesExcludingNothing.isEmpty()) {
                return BuiltinNothing
            }
            if (typesExcludingNothing.size == 1) {
                return typesExcludingNothing[0]
            }

            var pivot = typesExcludingNothing[0]
            for (_type in typesExcludingNothing[1..<typesExcludingNothing.size]) {
                var type = _type
                var swapped = false
                while (!(type isSubtypeOf pivot)) {
                    if (pivot.superTypes.isEmpty()) return BuiltinAny
                    if (pivot.superTypes.size > 1) {
                        if (swapped) {
                            return BuiltinAny
                        }
                        val temp = pivot
                        pivot = type
                        type = temp
                        swapped = true
                    }
                    else {
                        pivot = pivot.superTypes.iterator().next()
                    }
                }
            }

            return pivot
        }

        /**
         * @see [closestCommonSupertypeOf]
         */
        fun closestCommonSupertypeOf(vararg types: BaseType): BaseType {
            return closestCommonSupertypeOf(types.asList())
        }
    }
}