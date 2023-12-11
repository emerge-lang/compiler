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

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeReference
import compiler.binding.ObjectMember
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting
import java.util.IdentityHashMap

sealed interface ResolvedTypeReference {
    val context: CTContext
    val isNullable: Boolean
    val simpleName: String?

    /**
     * TODO: rename to mutability
     */
    val mutability: TypeMutability

    fun modifiedWith(modifier: TypeMutability): ResolvedTypeReference

    fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference

    fun withCombinedNullability(nullability: TypeReference.Nullability): ResolvedTypeReference

    /**
     * Validates the type reference.
     *
     * @return Any reportings on the validated code
     */
    fun validate(): Collection<Reporting>

    /**
     * Determines whether a value of type `this` can be assigned to a variable
     * of type [other].
     * @param assignmentLocation Will be used in the returned [Reporting]
     * @return `null` if the assignment is allowed, a reporting of level [Reporting.Level.ERROR] describing the
     * problem with the assignment in case it is not possible
     */
    fun evaluateAssignabilityTo(other: ResolvedTypeReference, assignmentLocation: SourceLocation): ValueNotAssignableReporting?

    /**
     * Compares the two types when a value of this type should be referenced by the given type.
     * @return The hierarchic distance (see [BaseType.hierarchicalDistanceTo]) if the assignment is possible,
     *         null otherwise.
     */
    fun assignMatchQuality(other: ResolvedTypeReference): Int?

    /**
     * @return `this` if the [mutability] set explicitly, a copy of `this` with the [mutability] set to [mutability] otherwise.
     */
    fun defaultMutabilityTo(mutability: TypeMutability?): ResolvedTypeReference

    /**
     * Finds the "greatest common denominator" of this type and the [other] type.
     * This method is associative:
     * * `a.closestCommonAncestorWith(b) == b.closestCommonAncestorWith(a)`
     * * `a.closestCommonAncestorWith(b).closestCommonAncestorWith(c) == b.closestCommonAncestorWith(c).closestCommonAncestorWith(a)`
     */
    fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference

    /**
     * If this type has a member vof
     */
    fun findMemberVariable(name: String): ObjectMember? = null

    /**
     * Used to derive information about generic types in concrete situations, so e.g.:
     *
     *     struct S<T> {
     *       prop: T
     *     }
     *
     *     val myS: S<Int> = ...
     *     val foo = myS.prop // here, unify is used to derive that `foo` is an `Int` now
     *
     * This is achieved by the mechanism that is copied from prolog:
     *
     * let `this` be `S<T>`
     * let `other` be `S<Int>`
     *
     * Then the two `S` will match, and the type arguments will be aligned with each other, associating the
     * `T` type parameter with the `Int` type argument: the result is `mapOf(T to Int)`
     *
     * Note that the names on both sides are kept isolated from each other. E.g. we might have another struct `F<T>`:
     *
     *     struct F<T> {
     *       someS: S<T>
     *     }
     *
     * here, the `T` from the declaration in `F` is distinct from the `T in the declaration of `S`. Say we obtained
     * a value not known more concretely of the type `S<T>` as declared in `F`:
     *
     *      fun foo<T>(f: F<T>) -> T = f.someS
     *
     * Then, when analyzing this expression:
     *
     * `foo<Int>(myF).prop`, one has to unify `S<T>` with `S<T>` with the two Ts being distinct. To handle this correctly,
     * this method works with [IdentityHashMap] on the `T`s.
     *
     * @param carry When multiple types have to be found at the same time (a function invocation with more than one parameter),
     *              one can carry the context/result between the unifications.
     * @throws TypesNotUnifiableException If two types are disjoint / their conjunction is empty (e.g. Boolean and Int)
     */
    fun unify(other: ResolvedTypeReference, carry: TypeUnification): TypeUnification {
        TODO()
    }

    /**
     * Adds the generic type information from [context] to this type, e.g.:
     *
     * * `this`: `Int`
     * * `contextTypes`: _any value_
     * * result: `Int`
     *
     *
     * * `this`: `T`
     * * `contextTypes`: T => `Boolean`
     * * result: `Boolean`
     *
     *
     * * `this`: `Array<E>`
     * * `contextTypes`: E => `Int`
     * * result: `Array<Int>`
     *
     *
     * * `this`: `T`
     * * `contextTypes`: E => `Int`
     * * result: `T`
     *
     * @param context the type of the parent context, e.g. `Array<Int>`
     */
    fun contextualize(context: TypeUnification, side: (TypeUnification) -> Map<String, BoundTypeArgument> = TypeUnification::left) = this

    /**
     * @return whether both types refer to the same base type or generic type parameter
     */
    fun hasSameBaseTypeAs(other: ResolvedTypeReference): Boolean

    /**
     * For parameterized types contains the bindings already resulting from that parameterization
     * in the [TypeUnification.left] part:
     *
     * given a `struct S<T>` [BaseType] and a `S<Int>` [ResolvedTypeReference], returns
     * `T => Int` in [TypeUnification.left]
     */
    val inherentTypeBindings: TypeUnification
        get() = TODO()
}

infix fun ResolvedTypeReference.isAssignableTo(other: ResolvedTypeReference): Boolean {
    return evaluateAssignabilityTo(other, SourceLocation.UNKNOWN) == null
}

class TypesNotUnifiableException(
    val left: ResolvedTypeReference,
    val right: ResolvedTypeReference,
    val reason: String
) : RuntimeException("Type $left cannot be unified with $right: $reason")