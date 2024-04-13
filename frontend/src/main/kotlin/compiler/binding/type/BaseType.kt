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

import compiler.ast.type.TypeArgument
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.BoundFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.DefinitionWithVisibility
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import kotlinext.get

/**
 * Base type are classes, interfaces, enums, built-in type
 */
interface BaseType : SemanticallyAnalyzable, DefinitionWithVisibility {
    val simpleName: String
        get() = javaClass.simpleName

    // TODO: infer this from declaring package and simpleName
    val canonicalName: CanonicalElementName.BaseType

    val baseReference: BoundTypeReference
        get() = RootResolvedTypeReference(TypeReference(this.simpleName), this, typeParameters.map {
                BoundTypeArgument(
                    TypeArgument(
                        TypeVariance.UNSPECIFIED,
                        TypeReference("_"),
                    ),
                    it.variance,
                    it.bound,
                )
            })

    val superTypes: Set<BaseType>
        get() = emptySet()

    /** TODO: make non-nullable as soon as ALL builtin types are declared in emerge source */
    val constructor: BoundFunction?
        get() = null

    val destructor: BoundFunction?
        get() = null

    val typeParameters: List<BoundTypeParameter>
        get() = emptyList()

    /**
     * If true, values of this type can by design not change. This is the case for primitives like booleans
     * and ints, but could also apply to classes who are declared as "immutable".
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
    fun resolveMemberFunction(name: String): Collection<BoundOverloadSet> = emptySet()

    fun resolveMemberVariable(name: String): BoundBaseTypeMemberVariable? = null

    fun toBackendIr(): IrBaseType

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return typeParameters.flatMap { it.semanticAnalysisPhase1() }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return typeParameters.flatMap { it.semanticAnalysisPhase2() }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return typeParameters.flatMap { it.semanticAnalysisPhase3() }
    }

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