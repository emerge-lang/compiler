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
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundParameter
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.basetype.BoundBaseType
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.binding.context.CTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Span
import compiler.util.twoElementPermutationsUnordered
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import java.util.IdentityHashMap

sealed interface BoundTypeReference {
    /** the context in which this reference exists / was bound */
    val context: CTContext

    val isNullable: Boolean

    /** todo: refactor into .toSimpleString(): String */
    val simpleName: String?

    val mutability: TypeMutability
    val span: Span?

    /**
     * Whether this type is a subtype of `read Nothing`
     */
    val isNonNullableNothing: Boolean

    /**
     * The [BoundBaseType] this type is referring to, as concrete as possible.
     */
    val baseTypeOfLowerBound: BoundBaseType

    /**
     * True if `this` is an [UnresolvedType] or whether any subcomponents of this type
     * are [isPartiallyUnresolved].
     */
    val isPartiallyUnresolved: Boolean

    /**
     * @return this type, with the given mutability if it doesn't explicitly have one. Also applied to type arguments,
     * though type arguments will never get [TypeMutability.EXCLUSIVE] and instead will get [TypeMutability.READONLY].
     */
    fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeReference

    /**
     * @return this type with the given [mutability], defaulting ([defaultMutabilityTo])
     * the mutability of type arguments to the given mutability.
     */
    fun withMutability(mutability: TypeMutability?): BoundTypeReference

    /**
     * @return this type but [mutability] is the result of [TypeMutability.union] of the
     * existing mutability and the given one. Type parameters will be defaulted ([defaultMutabilityTo])
     * to the resulting mutability.
     */
    fun withMutabilityUnionedWith(mutability: TypeMutability?): BoundTypeReference

    /**
     * @return this type but [limitToMutability] is the result of [TypeMutability.limitedTo] of the
     * existing mutability and the given one. Type parameters will also be modified with [withMutabilityLimitedTo].
     */
    fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference

    /**
     * @return this type but [isNullable] is according to the nullability given for this invocation. If that is
     * [TypeReference.Nullability.UNSPECIFIED], the existing value will be reused.
     */
    fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference

    /**
     * Validates the type reference. Must be invoked after [SemanticallyAnalyzable.semanticAnalysisPhase1].
     */
    fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis)

    /**
     * Determines whether a value of type `this` can be assigned to a variable
     * of type [targetType].
     * @param assignmentLocation Will be used in the returned [Diagnostic]
     * @return `null` if the assignment is allowed, a diagnostic of severity [Diagnostic.Severity.ERROR] describing the
     * problem with the assignment in case it is not possible
     */
    fun evaluateAssignabilityTo(targetType: BoundTypeReference, assignmentLocation: Span): ValueNotAssignableDiagnostic? {
        val unification = targetType.unify(this, assignmentLocation, TypeUnification.EMPTY)
        return unification.diagnostics.firstOrNull { it.severity >= Diagnostic.Severity.ERROR } as ValueNotAssignableDiagnostic?
    }

    /**
     * Finds the "greatest common denominator" of this type and the [other] type.
     * This method is associative:
     * * `a.closestCommonSupertypeWith(b) == b.closestCommonSupertypeWith(a)`
     * * `a.closestCommonSupertypeWith(b).closestCommonSupertypeWith(c) == b.closestCommonSupertypeWith(c).closestCommonSupertypeWith(a)`
     */
    fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference

    /**
     * @return a possible directly declared member variable of the type. Does not look for extension variables.
     */
    fun findMemberVariable(name: String): Set<BoundBaseTypeMemberVariable> = emptySet()

    fun findMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> = emptySet()

    /**
     * @return a recursive copy of this type where all [GenericTypeReference]s that reference one of the [variables]
     * are wrapped in a [TypeVariable] instance. This makes the resulting type subject to inferring generic types
     * in a call to [unify].
     */
    fun withTypeVariables(variables: Collection<BoundTypeParameter>): BoundTypeReference

    /**
     * Asserts that `assigneeType` is identical to or a subtype of `this`. Fills [TypeUnification.bindings]
     * with necessary values for type variables and fills [TypeUnification.diagnostics] with details about why
     * the assertion doesn't hold.
     *
     * Used to derive information about generic types in concrete situations, so e.g.:
     *
     *     class S<T> {
     *       prop: T
     *     }
     *
     *     val myS: S<out Any> = S::<S32>(2) // here, unify is used to determine that S<32> is assignable to S<out Any>
     *
     * This is achieved by the mechanism of unification that is copied from prolog (or logic programming in general):
     *
     * let `this` be `S<T>`
     * let `assigneeType` be `S<Int>`
     *
     * Then the two `S` will match, and the type arguments will be aligned with each other, associating the
     * `T` type parameter with the `Int` type argument: the result is `mapOf(T to Int)`
     *
     * Note that the names on both sides are kept isolated from each other. E.g. we might have another class `F<T>`:
     *
     *     class F<T> {
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
     * If two disjoint ([isDisjointWith]) types are to be unified the final type will remain with the first-come-first-serve
     * type and a [ValueNotAssignableDiagnostic] will be added to the [TypeUnification].
     *
     * The [Diagnostic]s added to [carry] will refer to `this` as the type being assigned to (member variable, function
     * parameter, ...) and [assigneeType] as the type of the value being assigned.
     *
     * @param assignmentLocation Used to properly locate errors, also for forwarding to [evaluateAssignabilityTo]
     * @param carry When multiple types have to be found at the same time (a function invocation with more than one parameter),
     *              one can carry the context/result between the unifications).
     */
    fun unify(assigneeType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): TypeUnification

    /**
     * Replaces [TypeVariable] in this type with their bindings from [context].
     * This does **not** replace [GenericTypeReference], use [instantiateAllParameters] for that!
     */
    fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference = this

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
    fun instantiateAllParameters(context: TypeUnification): BoundTypeReference

    /**
     * @return whether both types refer to the same base type or generic type parameter
     */
    fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean

    fun isDisjointWith(other: BoundTypeReference): Boolean {
        return !(this isAssignableTo other) && !(other isAssignableTo this)
    }

    /**
     * For parameterized types contains the bindings already resulting from that parameterization
     * in the [TypeUnification.left] part:
     *
     * given a `class S<T>` [BoundBaseTypeDefinition] and a `S<Int>` [BoundTypeReference], returns
     * `T => Int` in [TypeUnification.left]
     */
    val inherentTypeBindings: TypeUnification

    fun asAstReference(): TypeReference

    fun toBackendIr(): IrType

    companion object {
        /**
         * in contexts that support it (e.g. variable declarations), referencing a type with this name
         * will not actually try to resolve that type, but rather lead to that type being inferred.
         */
        const val NAME_REQUESTING_TYPE_INFERENCE = "_"
    }
}

fun List<BoundParameter>.nonDisjointPairs(): Sequence<Pair<BoundParameter, BoundParameter>> {
    /*
    this has approximately O(2n²) performance; not good. Maye it can be improved by implementing
    closestCommonSupertypeOf(List<BoundTypeReference>) and using it here. Thats pretty complex to do
    soll i'll do it if i can confirm that the overloading semantics based on this are actually good/what i want.
    */
    return this
        .filter { it.typeAtDeclarationTime != null }
        .twoElementPermutationsUnordered()
        .filterNot { (a, b) -> a.typeAtDeclarationTime!!.isDisjointWith(b.typeAtDeclarationTime!!) }
}

infix fun BoundTypeReference.isAssignableTo(other: BoundTypeReference): Boolean {
    return evaluateAssignabilityTo(other, Span.UNKNOWN) == null
}