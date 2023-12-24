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
import compiler.ast.type.TypeReference
import compiler.binding.ObjectMember
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting
import java.util.IdentityHashMap

sealed interface ResolvedTypeReference {
    // TODO: remove, is unused
    val context: CTContext
    val isNullable: Boolean
    val simpleName: String?

    val mutability: TypeMutability
    val sourceLocation: SourceLocation?

    /**
     * @return this type, with the given mutability if it doesn't explicitly have one.
     */
    fun defaultMutabilityTo(mutability: TypeMutability?): ResolvedTypeReference

    /**
     * @return this type with the given [mutability], defaulting ([defaultMutabilityTo])
     * the mutability of type arguments to the given mutablility.
     */
    fun withMutability(modifier: TypeMutability): ResolvedTypeReference

    /**
     * @return this type but the mutability is the result of [TypeMutability.combinedWith] of the
     * existing mutability and the given one. Type parameters will be defaulted ([defaultMutabilityTo])
     * to the resulting mutability.
     */
    fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference

    /**
     * @return this type but [isNullable] is according to the nullability given for this invocation. If that is
     * [TypeReference.Nullability.UNSPECIFIED], the existing value will be reused.
     */
    fun withCombinedNullability(nullability: TypeReference.Nullability): ResolvedTypeReference

    /**
     * Validates the type reference.
     *
     * @return Any reportings on the validated code
     */
    fun validate(forUsage: TypeUseSite): Collection<Reporting>

    /**
     * Determines whether a value of type `this` can be assigned to a variable
     * of type [other].
     * @param assignmentLocation Will be used in the returned [Reporting]
     * @return `null` if the assignment is allowed, a reporting of level [Reporting.Level.ERROR] describing the
     * problem with the assignment in case it is not possible
     */
    fun evaluateAssignabilityTo(other: ResolvedTypeReference, assignmentLocation: SourceLocation): ValueNotAssignableReporting?

    /**
     * Finds the "greatest common denominator" of this type and the [other] type.
     * This method is associative:
     * * `a.closestCommonAncestorWith(b) == b.closestCommonAncestorWith(a)`
     * * `a.closestCommonAncestorWith(b).closestCommonAncestorWith(c) == b.closestCommonAncestorWith(c).closestCommonAncestorWith(a)`
     */
    fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference

    /**
     * @return a possible directly declared member variable of the type. Does not look for extension variables.
     */
    fun findMemberVariable(name: String): ObjectMember? = null

    /**
     * Used to derive information about generic types in concrete situations, so e.g.:
     *
     *     struct S<T> {
     *       prop: T
     *     }
     *
     *     val myS: S<Int> = S(2)
     *     val foo = myS.prop // here, unify is used to derive that `foo` is an `Int` now
     *
     * This is achieved by the mechanism of unification that is copied from prolog (or logic programming in general):
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
    fun unify(other: ResolvedTypeReference, carry: TypeUnification): TypeUnification

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
    fun contextualize(context: TypeUnification, side: (TypeUnification) -> Map<String, ResolvedTypeReference> = TypeUnification::left) = this

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
}

infix fun ResolvedTypeReference.isAssignableTo(other: ResolvedTypeReference): Boolean {
    return evaluateAssignabilityTo(other, SourceLocation.UNKNOWN) == null
}