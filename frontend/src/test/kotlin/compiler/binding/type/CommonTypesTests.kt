package compiler.compiler.binding.type

import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.binding.type.BoundTypeReference
import io.kotest.assertions.withClue
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty

/**
 * What the proofs conjecture of [BoundTypeReference.intersect] and [BoundTypeReference.closestCommonSupertypeWith]
 * (in `type-system-proofs/theories`: `Conjectures.v`, `Constraints.closest_common_supertype_of_classes`,
 * `GenericArguments.closest_common_supertype_keeps_bottom_only`, `GenericCode.intersect_stays_in_generic_code`,
 * `GenericCode.closest_common_supertype_stays_in_generic_code`), checked for every pair of a set of types. A
 * conjecture about the types of a fragment claims nothing about others, so each check takes the pairs of it.
 *
 * Of two types of the fragment, `A?` and `P` with `P : Any?`, the intersection is `A? & P`, whose components keep
 * their nullability: of the fragment, and of the types of generic code (coverage #15).
 */
class CommonTypesTests : FreeSpec({
    val types = TypeGrid.types
    val ctxParameters = TypeGrid.ctxParameters

    fun violationsOf(
        of: (BoundTypeReference) -> Boolean = { true },
        check: (BoundTypeReference, BoundTypeReference) -> String?,
    ): List<String> {
        val inputs = types.filter { (_, t) -> of(t) }
        return inputs.flatMap { (aStr, a) ->
            inputs.mapNotNull { (bStr, b) ->
                try {
                    check(a, b)?.let { "$aStr, $bStr: $it" }
                } catch (e: Exception) {
                    "$aStr, $bStr: ${e::class.simpleName} ${e.message}"
                }
            }
        }
    }

    fun List<String>.shouldBeNone() {
        withClue(joinToString("\n")) {
            shouldBeEmpty()
        }
    }

    "the grid has types of each fragment" {
        types.filterNot { (_, t) -> t.isClassType() }.map { it.first }.let { check(it.size < types.size - 10) { it } }
        types.filter { (_, t) -> t.isClassType() && !t.isWithoutContravariance() }.let { check(it.isNotEmpty()) }
        types.filterNot { (_, t) -> t.isOfFragment() && t.isOfGenericCode(ctxParameters) }.map { it.first }
            .let { check(it.isEmpty()) { it } }
        types.filter { (_, t) -> t.keepsNullableComponents() }.map { it.first }
            .let { check(it == listOf(
                "A? & P", "P & R", "Nothing? & P", "A? & R? & P", "A? & B? & P", "P & R & A?", "R & B?", "mut R & mut B?",
                "D? & P", "U & R", "A? & U", "U & P",
            )) { it } }
    }

    "the closest common supertype is above both types" {
        violationsOf { a, b ->
            val supertype = a.closestCommonSupertypeWith(b)
            supertype.takeUnless { a.isBelow(it) && b.isBelow(it) }?.toString()
        }.shouldBeNone()
    }

    "the intersection is below both types" {
        violationsOf { a, b ->
            val intersection = a.intersect(b)
            intersection.takeUnless { it.isBelow(a) && it.isBelow(b) }?.toString()
        }.shouldBeNone()
    }

    "the intersection of types of the fragment that don't keep their nullability is of it" {
        violationsOf(BoundTypeReference::isOfFragment) { a, b ->
            if (keepsNullability(a, b)) null else a.intersect(b)
                .takeUnless { it.isOfFragment() && (!it.isBareNullable() || a.isBareNullable() || b.isBareNullable()) }
                ?.toString()
        }.shouldBeNone()
    }

    "the intersection of types of the fragment is of it" {
        violationsOf(BoundTypeReference::isOfFragment) { a, b ->
            a.intersect(b).takeUnless { it.isOfFragment() }?.toString()
        }.shouldBeNone()
    }

    "the closest common supertype of types of the fragment is of it" {
        violationsOf(BoundTypeReference::isOfFragment) { a, b ->
            a.closestCommonSupertypeWith(b)
                .takeUnless { it.isOfFragment() && (!it.isBareNullable() || a.isBareNullable() || b.isBareNullable()) }
                ?.toString()
        }.shouldBeNone()
    }

    "the intersection of types of generic code is of it" {
        violationsOf({ it.isOfFragment() && it.isOfGenericCode(ctxParameters) }) { a, b ->
            a.intersect(b)
                .takeUnless { it.isOfGenericCode(a.mentionedParameters() + b.mentionedParameters()) }
                ?.toString()
        }.shouldBeNone()
    }

    "the closest common supertype of types of generic code is of it" {
        violationsOf({ it.isOfFragment() && it.isOfGenericCode(ctxParameters) }) { a, b ->
            a.closestCommonSupertypeWith(b)
                .takeUnless { it.isOfGenericCode(a.mentionedParameters() + b.mentionedParameters()) }
                ?.toString()
        }.shouldBeNone()
    }

    "the closest common supertype of class types without contravariance is one, without contravariance" {
        violationsOf({ it.isClassType() && it.isWithoutContravariance() }) { a, b ->
            a.closestCommonSupertypeWith(b).takeUnless { it.isClassType() && it.isWithoutContravariance() }?.toString()
        }.shouldBeNone()
    }

    "the closest common supertype of types that mention Nothing only as Nothing mentions it only so" {
        violationsOf({ it.isOfFragment() && it.isBottomOnly() }) { a, b ->
            a.closestCommonSupertypeWith(b).takeUnless { it.isBottomOnly() }?.toString()
        }.shouldBeNone()
    }

    val instantiations = TypeGrid.instantiations

    "the instance of the intersection is below the instances of both types" {
        instantiations.flatMap { (ctxStr, bindings) ->
            violationsOf { a, b ->
                val intersection = a.intersect(b).instantiateAllParameters(bindings)
                val aInstance = a.instantiateAllParameters(bindings)
                val bInstance = b.instantiateAllParameters(bindings)
                intersection
                    .takeUnless { it.isBelow(aInstance) && it.isBelow(bInstance) }
                    ?.let { "in $ctxStr: $it, of $aInstance and $bInstance" }
            }
        }.shouldBeNone()
    }
})
