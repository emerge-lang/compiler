package compiler.binding.type

import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance

/**
 * What the static type of a value tells about checking it against a type at runtime, with `is` or `as`.
 */
internal sealed interface StaticTypeCheckResult {
    /** every value of the static type is one of the checked type: the check tells nothing */
    data object AlwaysSucceeds : StaticTypeCheckResult

    /**
     * No value of the static type is one of the checked type.
     * @param reason completes the sentence "this can never succeed: ..."
     */
    data class NeverSucceeds(val reason: String) : StaticTypeCheckResult

    /** up to the value */
    data object Unknown : StaticTypeCheckResult
}

/**
 * @param typeOfValue the static type of the value being checked
 * @param typeToCheck the type the value is checked against at runtime, see `emerge.core.reflection.isInstanceOf`
 * @return what is known of the check without running it. [StaticTypeCheckResult.NeverSucceeds] is not complete:
 * it is found where telling takes no more than the two types, see [whyNoValueIsOf].
 */
internal fun staticResultOfTypeCheck(typeOfValue: BoundTypeReference, typeToCheck: BoundTypeReference): StaticTypeCheckResult {
    if (typeOfValue.isPartiallyUnresolved || typeToCheck.isPartiallyUnresolved) {
        return StaticTypeCheckResult.Unknown
    }
    if (typeOfValue.mentionsTypeVariables() || typeToCheck.mentionsTypeVariables()) {
        return StaticTypeCheckResult.Unknown
    }
    if (typeOfValue.isNonNullableNothing) {
        // there is no value, the check is never run. That is the business of the code that is unreachable for it
        return StaticTypeCheckResult.Unknown
    }
    if (typeOfValue isAssignableTo typeToCheck) {
        return StaticTypeCheckResult.AlwaysSucceeds
    }

    return typeOfValue.whyNoValueIsOf(typeToCheck)
        ?.let(StaticTypeCheckResult::NeverSucceeds)
        ?: StaticTypeCheckResult.Unknown
}

/**
 * The object a reference of type `this` refers to is of a class that is a subtype of `this`, and with the mutability
 * of the reference, it is the value that is checked against [target] (`emerge.core.reflection.isInstanceOf`). This
 * finds the cases where there cannot be a class of which a value of `this` is one of [target]:
 * * the value is never `null`, or always, and the other type has it the other way around
 * * one of the types names a class, which has no subtypes, and that is no subtype of what the other type names.
 *   This is more than the intersection of the two types being `Nothing`, which takes two classes: here, a class
 *   and an interface it doesn't implement do
 * * the type arguments of the two types for the same base type have no type in common
 * * [target] asks for a mutability that the reference doesn't have, and the object is known not to be of a
 *   class that is `const` by itself, for which that wouldn't matter. The intersection doesn't tell this either:
 *   that of a `read Foo` and a `mut Foo` is a `mut Foo`
 *
 * @return why no value of this type is one of [target]; `null` if that isn't known
 */
private fun BoundTypeReference.whyNoValueIsOf(target: BoundTypeReference): String? {
    if (this.isNullable && target.isNullable) {
        // null is a value of both
        return null
    }

    val nonNullableSelf = this.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)
    val nonNullableTarget = target.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE)
    if (nonNullableSelf.isNonNullableNothing) {
        return "the value is always null, which is no value of $target"
    }
    if (nonNullableTarget.isNonNullableNothing) {
        return if (target.isNullable) {
            "the only value of $target is null, which a value of type $this never is"
        } else {
            "$target has no values"
        }
    }

    val ownComponents = this.namedComponents()
    val targetComponents = target.namedComponents()
    for (own in ownComponents) {
        for (targeted in targetComponents) {
            if (!own.baseType.kind.allowsSubtypes && !(own.baseType isSubtypeOf targeted.baseType)) {
                return "the value is a ${own.baseType.simpleName}, which is no subtype of ${targeted.baseType.simpleName}"
            }
            if (!targeted.baseType.kind.allowsSubtypes && !(targeted.baseType isSubtypeOf own.baseType)) {
                return "the value is a ${own.baseType.simpleName}, and ${targeted.baseType.simpleName} is no subtype of that"
            }
            if (own.hasNoParameterizationInCommonWith(targeted)) {
                return "the type arguments of $own and $targeted have no type in common"
            }
        }
    }

    // an object of a class that is const by itself is a value of any mutability, whatever the reference says
    val objectMayBeOfConstClass = (ownComponents + targetComponents).none { !it.baseType.kind.allowsSubtypes && !it.baseType.isConst }
    // the mutability of a type parameter is that of the type argument, known at runtime
    val mutabilityOfReferenceIsKnown = !this.isOrIntersectsTypeParameter()
    if (mutabilityOfReferenceIsKnown && !objectMayBeOfConstClass && !(this.assignmentMutability isAssignableTo target.assignmentMutability)) {
        return "the value is referred to as ${this.mutability.keyword.text}, and an object doesn't know the mutability of the references to it. A check can only keep or weaken it, ${target.mutability.keyword.text} is neither"
    }

    return null
}

/**
 * The named types that every value of this type is a value of, nullability aside. Of a type parameter, those are
 * the ones of its bound.
 */
private fun BoundTypeReference.namedComponents(visitedParameters: Set<BoundTypeParameter> = emptySet()): List<RootResolvedTypeReference> = when (this) {
    is RootResolvedTypeReference -> listOf(this)
    is NullableTypeReference -> nested.namedComponents(visitedParameters)
    is BoundTypeArgument -> type.namedComponents(visitedParameters)
    is GenericTypeReference -> if (parameter in visitedParameters) emptyList() else effectiveBound.namedComponents(visitedParameters + parameter)
    is BoundIntersectionTypeReference -> components.flatMap { it.namedComponents(visitedParameters) }
    is ErroneousType,
    is TypeVariable -> emptyList()
}

private fun BoundTypeReference.isOrIntersectsTypeParameter(): Boolean = when (this) {
    is GenericTypeReference -> true
    is NullableTypeReference -> nested.isOrIntersectsTypeParameter()
    is BoundIntersectionTypeReference -> components.any { it.isOrIntersectsTypeParameter() }
    is BoundTypeArgument -> type.isOrIntersectsTypeParameter()
    is RootResolvedTypeReference,
    is ErroneousType,
    is TypeVariable -> false
}

/**
 * An object has one parameterization for each of its base types, so where this type and [other] ask for
 * parameterizations of the same base type that no type satisfies both, no object is of both types.
 *
 * Where the base types differ, that of the subtype is translated to the supertype. That is exact only where the
 * subtype has all exact arguments: of a `Nest<out A>` with `class Nest<E> : Seq<Box<E>>`, the `Seq` is a
 * `Seq<Box<X>>` for some `X` below `A`, which is no type argument that could be written.
 */
private fun RootResolvedTypeReference.hasNoParameterizationInCommonWith(other: RootResolvedTypeReference): Boolean {
    val ownAtCommonBase: RootResolvedTypeReference
    val otherAtCommonBase: RootResolvedTypeReference
    when {
        this.baseType == other.baseType -> {
            ownAtCommonBase = this
            otherAtCommonBase = other
        }
        this.isTranslatableTo(other) -> {
            ownAtCommonBase = this.getInstantiatedSupertype(other.baseType)
            otherAtCommonBase = other
        }
        other.isTranslatableTo(this) -> {
            ownAtCommonBase = this
            otherAtCommonBase = other.getInstantiatedSupertype(this.baseType)
        }
        else -> return false
    }

    val ownArguments = ownAtCommonBase.arguments ?: return false
    val otherArguments = otherAtCommonBase.arguments ?: return false
    return ownArguments.zip(otherArguments).any { (ownArgument, otherArgument) -> ownArgument.hasNoTypeInCommonWith(otherArgument) }
}

/**
 * Whether [RootResolvedTypeReference.getInstantiatedSupertype] gives all there is to know of the parameterization
 * that the objects of this type have for the base type of [supertype].
 */
private fun RootResolvedTypeReference.isTranslatableTo(supertype: RootResolvedTypeReference): Boolean {
    if (supertype.baseType.typeParameters.isNullOrEmpty() || this.baseType == context.swCtx.nothing) {
        return false
    }
    if (!(this.baseType isSubtypeOf supertype.baseType)) {
        return false
    }

    val ownArguments = this.arguments ?: emptyList()
    return ownArguments.size == (this.baseType.typeParameters?.size ?: 0)
        && ownArguments.all { it.variance == TypeVariance.UNSPECIFIED }
}

/**
 * Whether there is no type that is an argument for both of these: an exact argument is one for itself only, an
 * `out` one for all of its subtypes, and an `in` one for all of its supertypes. Two `out` arguments always have
 * `Nothing` in common, two `in` ones the top type.
 *
 * Not known where a type parameter is mentioned: what it is bound to is known at runtime.
 */
private fun BoundTypeArgument.hasNoTypeInCommonWith(other: BoundTypeArgument): Boolean {
    if (this.type.mentionsTypeParameters() || other.type.mentionsTypeParameters()) {
        return false
    }

    return when (this.variance) {
        TypeVariance.UNSPECIFIED -> when (other.variance) {
            TypeVariance.UNSPECIFIED -> !(this.type isAssignableTo other.type) || !(other.type isAssignableTo this.type)
            TypeVariance.OUT -> !(this.type isAssignableTo other.type)
            TypeVariance.IN -> !(other.type isAssignableTo this.type)
        }
        TypeVariance.OUT -> when (other.variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.IN -> !(other.type isAssignableTo this.type)
            TypeVariance.OUT -> false
        }
        TypeVariance.IN -> when (other.variance) {
            TypeVariance.UNSPECIFIED,
            TypeVariance.OUT -> !(this.type isAssignableTo other.type)
            TypeVariance.IN -> false
        }
    }
}
