package compiler.binding.expression

import compiler.ast.type.AstSpecificTypeArgument
import compiler.ast.type.AstWildcardTypeArgument
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeVariance
import compiler.binding.type.BoundIntersectionTypeReference
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.NullableTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.forbiddenCast
import compiler.lexer.Span

/**
 * The runtime checks a cast against the base types, type arguments and nullability of the target type. It doesn't
 * know mutability: an `Array<mut Foo>` and an `Array<const Foo>` are the same to it. So a cast must not claim a
 * mutability that the type of the value doesn't prove already.
 *
 * * of the value itself, the cast can keep or weaken the mutability (`x: read Any`, `x as read Foo`), not
 *   strengthen it (`x as mut Foo`), and `own` is never the target of a cast
 * * of a type argument, the type of the value proves the mutability only where it has the same base type as the
 *   target, in an argument that reads: `Array<out mut Foo>` proves that an `Array<Bar>` is an `Array<mut Bar>`.
 *   Without that, all that is known of a `Foo` in a type argument is that it reads as a `read Foo`: an invariant
 *   argument `Array<Foo>` is taken as `Array<out read Foo>`, and other mutabilities and `in` are errors.
 *   Types that are const by themselves (`String`, `S32`) need no proof.
 *
 * @param target the type as written in the cast, never nullable just for the cast being `as?`
 * @param source the type of the value being cast
 * @return the type the cast results in; differs from [target] in the variance of type arguments
 */
internal fun BoundCastExpression.soundCastTargetType(
    target: BoundTypeReference,
    source: BoundTypeReference,
    diagnosis: Diagnosis,
): BoundTypeReference {
    val reportAt = declaration.toType.span ?: declaration.span
    if (target.mutability == TypeMutability.OWN && !target.isInherentlyConst) {
        diagnosis.forbiddenCast(this, "Cannot cast to an own type: a cast cannot tell whether there are other references to the value.", reportAt)
    } else if (!target.isInherentlyConst && !source.mutability.isAssignableTo(target.mutability)) {
        diagnosis.forbiddenCast(
            this,
            "Cannot cast a ${source.mutability.keyword.text} value to a ${target.mutability.keyword.text} type: casts are not checked for mutability at runtime, they can only keep or weaken it.",
            reportAt,
        )
    }

    return CastTargetAdapter(this, diagnosis, reportAt).adapt(target, source)
}

private val BoundTypeReference.isInherentlyConst: Boolean
    get() = when (this) {
        is RootResolvedTypeReference -> baseType.isConst
        is NullableTypeReference -> nested.isInherentlyConst
        is BoundTypeArgument -> type.isInherentlyConst
        else -> false
    }

/** const by itself, and no type arguments that could say otherwise about what the object refers to */
private val BoundTypeReference.isMutabilityFree: Boolean
    get() = when (this) {
        is RootResolvedTypeReference -> baseType.isConst && arguments.isNullOrEmpty()
        is NullableTypeReference -> nested.isMutabilityFree
        else -> false
    }

private class CastTargetAdapter(
    val cast: BoundCastExpression,
    val diagnosis: Diagnosis,
    val reportAt: Span,
) {
    /**
     * @param source what is known statically of the value [target] describes; `null` if nothing
     */
    fun adapt(target: BoundTypeReference, source: BoundTypeReference?): BoundTypeReference = when (target) {
        is NullableTypeReference -> {
            val nested = adapt(target.nested, source)
            if (nested === target.nested) target else NullableTypeReference(nested)
        }
        is RootResolvedTypeReference -> adaptArguments(target, source)
        is BoundIntersectionTypeReference -> {
            // the components that are not adapted are not rebuilt, either; an intersection with type arguments as the
            // target of a cast is rare enough to leave the arguments of its components to be unproven
            target.components.forEach { adapt(it, null) }
            target
        }
        else -> target
    }

    private fun adaptArguments(target: RootResolvedTypeReference, source: BoundTypeReference?): BoundTypeReference {
        val targetArguments = target.arguments
        if (targetArguments.isNullOrEmpty()) {
            return target
        }

        val sourceOfSameBaseType = generateSequence(source) { (it as? NullableTypeReference)?.nested ?: (it as? BoundTypeArgument)?.type }
            .filterIsInstance<RootResolvedTypeReference>()
            .firstOrNull()
            ?.takeIf { it.baseType == target.baseType && it.arguments?.size == targetArguments.size }

        val adaptedArguments = targetArguments.mapIndexed { index, targetArgument ->
            adaptArgument(targetArgument, sourceOfSameBaseType?.arguments?.get(index))
        }
        if (adaptedArguments.indices.all { adaptedArguments[it] === targetArguments[it] }) {
            return target
        }

        return RootResolvedTypeReference(target.context, target.mutability, target.baseType, adaptedArguments)
    }

    private fun adaptArgument(target: BoundTypeArgument, source: BoundTypeArgument?): BoundTypeArgument {
        if (target.astNode is AstWildcardTypeArgument) {
            // the bound of the type parameter; every type argument is within it, mutability included
            return target
        }

        when (source?.variance) {
            TypeVariance.UNSPECIFIED -> {
                // the type argument of the value is exactly that of the source
                if (source.evaluateAssignabilityTo(target, reportAt) == null) {
                    return target
                }
                // and with that, it also is what an `out` argument of that type says
                return adaptArgumentOfReadableSource(target, source)
            }
            TypeVariance.OUT -> return adaptArgumentOfReadableSource(target, source)
            TypeVariance.IN, null -> return adaptUnprovenArgument(target)
        }
    }

    /**
     * @param source an `out` argument: the type argument of the value is a subtype of its type. For mutability
     * that means: exactly that of [source] if that is `mut` or `const`, and unknown if it is `read`.
     */
    private fun adaptArgumentOfReadableSource(target: BoundTypeArgument, source: BoundTypeArgument): BoundTypeArgument {
        val sourceMutability = source.type.mutability
        val targetMutability = target.type.mutability
        val nestedType = adapt(target.type, source.type)
        when (target.variance) {
            TypeVariance.IN -> {
                reportUncheckedInVariance(target)
                return target
            }
            TypeVariance.OUT -> {
                if (!target.type.isInherentlyConst && !sourceMutability.isAssignableTo(targetMutability)) {
                    reportUnprovenMutability(target)
                }
                return target.withType(nestedType, TypeVariance.OUT)
            }
            TypeVariance.UNSPECIFIED -> {
                if (target.type.isMutabilityFree) {
                    return target
                }
                if (sourceMutability != TypeMutability.READONLY && sourceMutability == targetMutability && nestedType === target.type) {
                    // exactly the mutability the source proves
                    return target
                }
                if (targetMutability != TypeMutability.READONLY && sourceMutability != targetMutability && !target.type.isInherentlyConst) {
                    reportUnprovenMutability(target)
                }
                return target.withType(nestedType, TypeVariance.OUT)
            }
        }
    }

    /** nothing is known statically about the type argument of the value */
    private fun adaptUnprovenArgument(target: BoundTypeArgument): BoundTypeArgument {
        if (target.variance == TypeVariance.IN) {
            reportUncheckedInVariance(target)
            return target
        }

        if (target.type.isMutabilityFree) {
            return target
        }

        if (target.type.mutability != TypeMutability.READONLY && !target.type.isInherentlyConst) {
            reportUnprovenMutability(target)
        }

        return target.withType(adapt(target.type, null), TypeVariance.OUT)
    }

    private fun BoundTypeArgument.withType(newType: BoundTypeReference, newVariance: TypeVariance): BoundTypeArgument {
        if (newType === type && newVariance == variance) {
            return this
        }

        return BoundTypeArgument(context, AstSpecificTypeArgument(newVariance, newType.asAstReference()), newVariance, newType)
    }

    private fun reportUnprovenMutability(target: BoundTypeArgument) {
        diagnosis.forbiddenCast(
            cast,
            "Casts are not checked for mutability at runtime, and the type of the value doesn't prove that the type argument is ${target.type.mutability.keyword.text}. Use `out read` here.",
            target.span ?: reportAt,
        )
    }

    private fun reportUncheckedInVariance(target: BoundTypeArgument) {
        diagnosis.forbiddenCast(
            cast,
            "Casts are not checked for mutability at runtime, so a cast cannot tell what an object takes for this type argument. Only `out` type arguments can be the target of a cast.",
            target.span ?: reportAt,
        )
    }
}
