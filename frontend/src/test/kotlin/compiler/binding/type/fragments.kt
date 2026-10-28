package compiler.compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.type.BoundIntersectionTypeReference
import compiler.binding.type.BoundTypeParameter
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.GenericTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.lexer.Span

/*
 * The sets of types the proofs in `type-system-proofs/theories` are about, as predicates on the types of the
 * frontend, so tests can check of the frontend what the proofs conjecture of it. Each mirrors the Rocq
 * definition it is named after.
 */

internal fun BoundTypeReference.isBelow(other: BoundTypeReference) = evaluateAssignabilityTo(other, Span.UNKNOWN) == null

private val RootResolvedTypeReference.typeArguments get() = arguments ?: emptyList()

private fun RootResolvedTypeReference.hasAllTypeArguments() = typeArguments.size == (baseType.typeParameters?.size ?: 0)

/** `exclusive Nothing`, with [RootResolvedTypeReference.baseType] Nothing (`Transitivity.is_bottom`) */
private fun RootResolvedTypeReference.isBottom() = mutability == TypeMutability.EXCLUSIVE && typeArguments.isEmpty()

private fun RootResolvedTypeReference.isNothing() = baseType == context.swCtx.nothing

/** `Fragment.is_component` */
private fun BoundTypeReference.isComponent() = this is RootResolvedTypeReference || (this is GenericTypeReference && !isNullable)

/** `Fragment.non_null` */
private fun BoundTypeReference.isNonNull() = if (this is BoundIntersectionTypeReference) !isNullable else isComponent()

/** `Fragment.gfrag`: the types of type parameters and intersections the proofs cover */
internal fun BoundTypeReference.isOfFragment(): Boolean = when (this) {
    is RootResolvedTypeReference -> hasAllTypeArguments() && typeArguments.all { it.type.isOfFragment() }
    is NullableTypeReference -> nested.isNonNull() && nested.isOfFragment()
    is GenericTypeReference -> !hasTypeVariables
    is BoundIntersectionTypeReference -> components.isNotEmpty()
        && components.all { it.isComponent() && it.isOfFragment() && it.assignmentMutability == assignmentMutability }
    else -> false
}

/** `Inference.afrag` and `Substitution.closed`: class types, mentioning Nothing only as `exclusive Nothing` */
internal fun BoundTypeReference.isClassType(): Boolean = when (this) {
    is RootResolvedTypeReference -> hasAllTypeArguments() && (!isNothing() || isBottom()) && typeArguments.all { it.type.isClassType() }
    is NullableTypeReference -> nested is RootResolvedTypeReference && nested.isClassType()
    else -> false
}

/** `GenericArguments.bottom_only`: mentions Nothing only as `exclusive Nothing`, also in the bounds of the parameters it refers to */
internal fun BoundTypeReference.isBottomOnly(): Boolean = bottomOnly(this, emptySet())

private fun bottomOnly(t: BoundTypeReference, visiting: Set<BoundTypeParameter>): Boolean = when (t) {
    is RootResolvedTypeReference -> (!t.isNothing() || t.isBottom()) && t.typeArguments.all { bottomOnly(it.type, visiting) }
    is NullableTypeReference -> bottomOnly(t.nested, visiting)
    is GenericTypeReference -> !t.effectiveBound.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE).isNonNullableNothing
        && (t.parameter in visiting || bottomOnly(t.parameter.bound, visiting + t.parameter))
    is BoundIntersectionTypeReference -> !t.isNonNullableNothing && t.components.all { bottomOnly(it, visiting) }
    else -> true
}

/**
 * `GenericCode.caller_type`: the types of generic code with the type parameters [parameters]: of the wide fragment
 * (`SubstitutionWide.wtfrag`), mentioning no other type parameters (`WithinBounds.mentions_only`)
 */
internal fun BoundTypeReference.isOfGenericCode(parameters: Set<String>): Boolean = isWide(this) && mentionsOnly(this, parameters, emptySet())

/** `Substitution.as_written` of a reference */
private fun GenericTypeReference.isAsWritten() =
    (givenMutability?.let { effectiveBound.assignmentMutability.isAssignableTo(it) } ?: true)
        && (!isNarrowed || !effectiveBound.isNullable)

/** `Substitution.is_component_shape` */
private fun BoundTypeReference.isComponentShape() = (this is RootResolvedTypeReference || this is GenericTypeReference) && !isNullable

private fun BoundTypeReference.intersectionComponents(): List<BoundTypeReference>? = when (this) {
    is BoundIntersectionTypeReference -> components
    is NullableTypeReference -> (nested as? BoundIntersectionTypeReference)?.components
    else -> null
}

/** the shape the `tfrag` family gives intersections, at the top or, in the wide fragment, as type arguments */
private fun intersectionOf(components: List<BoundTypeReference>, ofComponent: (BoundTypeReference) -> Boolean) =
    components.size >= 2 && components.all { it.isComponentShape() && ofComponent(it) }

/**
 * An intersection with a component that keeps its nullability, `A? & P` with `P : Any?`, as ofComponents makes it
 * where null is a value exactly where it is one of each component: outside of every fragment (coverage #15)
 */
internal fun BoundTypeReference.keepsNullableComponents(): Boolean = intersectionComponents()?.any { it.isNullable } == true

/** `SubstitutionWide.wtfrag` */
private fun isWide(t: BoundTypeReference): Boolean = t.intersectionComponents()?.let { intersectionOf(it, ::isWideBelowTop) } ?: isWideBelowTop(t)

/** `SubstitutionWide.wfrag` */
private fun isWideBelowTop(t: BoundTypeReference): Boolean = when (t) {
    is RootResolvedTypeReference -> if (t.isNothing()) t.isBottom() else t.hasAllTypeArguments() && t.typeArguments.all { isWide(it.type) }
    is NullableTypeReference -> (t.nested is RootResolvedTypeReference || t.nested is GenericTypeReference) && isWideBelowTop(t.nested)
    is GenericTypeReference -> isInstantiable(t, emptySet())
    else -> false
}

/**
 * `Substitution.sfrag`, `sfrag_h`: of the effective bound of a reference, the top (`top_tfrag`); of the declared
 * bound of its parameter, the whole (`param_tfrag`), [visiting] being the parameters whose bounds are being looked
 * at, which F-bounds mention again. Of a reference at the top of a bound, [visiting] is null: `sfrag_top_h`.
 */
private fun isInstantiable(t: BoundTypeReference, visiting: Set<BoundTypeParameter>?): Boolean = when (t) {
    is RootResolvedTypeReference -> if (t.isNothing()) t.isBottom() else t.hasAllTypeArguments()
        && (visiting == null || t.typeArguments.all { isInstantiable(it.type, visiting) })
    is NullableTypeReference -> (t.nested is RootResolvedTypeReference || t.nested is GenericTypeReference) && isInstantiable(t.nested, visiting)
    is GenericTypeReference -> t.isAsWritten() && !t.hasTypeVariables
        && isInstantiableTop(t.effectiveBound, null)
        && (visiting == null || t.parameter in visiting || isInstantiableTop(t.parameter.bound, visiting + t.parameter))
    else -> false
}

/** `Substitution.tfrag_h`, `tfrag_top_h` */
private fun isInstantiableTop(t: BoundTypeReference, visiting: Set<BoundTypeParameter>?): Boolean =
    t.intersectionComponents()?.let { intersectionOf(it) { c -> isInstantiable(c, visiting) } } ?: isInstantiable(t, visiting)

private fun mentionsOnly(t: BoundTypeReference, parameters: Set<String>, visiting: Set<BoundTypeParameter>): Boolean = when (t) {
    is RootResolvedTypeReference -> t.typeArguments.all { mentionsOnly(it.type, parameters, visiting) }
    is NullableTypeReference -> mentionsOnly(t.nested, parameters, visiting)
    is GenericTypeReference -> t.parameter.name in parameters && !t.hasTypeVariables
        && (t.parameter in visiting || mentionsOnly(t.parameter.bound, parameters, visiting + t.parameter))
    is BoundIntersectionTypeReference -> t.components.all { mentionsOnly(it, parameters, visiting) }
    else -> true
}
