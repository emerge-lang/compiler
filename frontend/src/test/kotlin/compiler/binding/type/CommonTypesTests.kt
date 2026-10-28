package compiler.compiler.binding.type

import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.binding.type.BoundTypeReference
import compiler.compiler.negative.validateModule
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
 * Of two types of the fragment, `A?` and `P` with `P : Any?`, the intersection is `A? & P`, outside of it: the
 * conjectures that intersections stay in the fragments are false there, and the checks leave such intersections
 * out until the proofs cover them (coverage #15).
 */
class CommonTypesTests : FreeSpec({
    val swCtx = validateModule("""
        interface A {}
        interface B {}
        interface C : A {}
        interface Ord<T> {}
        class N : Ord<N> {}
        class Box<E> {}
        class Ctx<P, Q : A, R : A?, F : Ord<in F>> {}
    """.trimIndent()).first

    val ctxParameters = setOf("P", "Q", "R", "F")

    val types = listOf(
        "A", "mut A", "const A", "exclusive A", "A?", "mut A?",
        "B", "const B?",
        "C", "mut C", "exclusive C?",
        "N", "mut N", "Ord<N>", "Ord<in N>",
        "Any", "Any?", "mut Any", "exclusive Nothing", "exclusive Nothing?",
        "Box<A>", "Box<C>", "Box<in A>", "Box<out A>", "Box<in C>", "Box<out C>", "Box<mut A>", "Box<A?>", "mut Box<out A>?",
        "Box<A & B>", "Box<out A & Q>", "Box<exclusive Nothing>",
        "P", "P?", "P!", "mut P", "Q", "const Q", "Q?", "R", "R!", "R?", "read R", "mut R?",
        "F", "F?", "mut F", "Ord<in F>",
        "Box<P>", "Box<P?>", "Box<out Q>", "Box<R!>", "Box<R?>", "Box<mut R>", "Box<F>",
        "A & B", "mut A & B", "A? & B?", "C & Q", "Q & B", "A & B & Q", "A & P", "mut A & R", "B & F", "A? & R?",
        // components that keep their nullability (coverage #15)
        "A? & P", "P & R",
    ).map { it to swCtx.parseTypeIn("Ctx", it) }

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
        types.filterNot { (_, t) -> t.isOfFragment() && t.isOfGenericCode(ctxParameters) }.map { it.first }
            .let { check(it == listOf("A? & P", "P & R")) { it } }
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

    "the intersection of types of the fragment is of it" {
        violationsOf(BoundTypeReference::isOfFragment) { a, b ->
            a.intersect(b).takeUnless { it.isOfFragment() || it.keepsNullableComponents() }?.toString()
        }.shouldBeNone()
    }

    "the closest common supertype of types of the fragment is of it" {
        violationsOf(BoundTypeReference::isOfFragment) { a, b ->
            a.closestCommonSupertypeWith(b).takeUnless { it.isOfFragment() }?.toString()
        }.shouldBeNone()
    }

    "the intersection of types of generic code is of it" {
        violationsOf({ it.isOfFragment() && it.isOfGenericCode(ctxParameters) }) { a, b ->
            a.intersect(b).takeUnless { it.isOfGenericCode(ctxParameters) || it.keepsNullableComponents() }?.toString()
        }.shouldBeNone()
    }

    "the closest common supertype of types of generic code is of it" {
        violationsOf({ it.isOfFragment() && it.isOfGenericCode(ctxParameters) }) { a, b ->
            a.closestCommonSupertypeWith(b).takeUnless { it.isOfGenericCode(ctxParameters) }?.toString()
        }.shouldBeNone()
    }

    "the closest common supertype of class types is one" {
        violationsOf(BoundTypeReference::isClassType) { a, b ->
            a.closestCommonSupertypeWith(b).takeUnless { it.isClassType() }?.toString()
        }.shouldBeNone()
    }

    "the closest common supertype of types that mention Nothing only as exclusive Nothing mentions it only so" {
        violationsOf({ it.isOfFragment() && it.isBottomOnly() }) { a, b ->
            a.closestCommonSupertypeWith(b).takeUnless { it.isBottomOnly() }?.toString()
        }.shouldBeNone()
    }

    // the type parameters of Ctx, bound in ways that tell their mutability and nullability apart
    val instantiations = listOf(
        "Ctx<mut A, mut C, A?, N>",
        "Ctx<const A, C, mut C, mut N>",
        "Ctx<A?, const A, const C?, const N>",
        "Ctx<exclusive C, exclusive C, exclusive Nothing?, exclusive N>",
        "Ctx<mut Box<A>?, mut A, mut A?, N>",
    ).map { it to swCtx.parseType(it).inherentTypeBindings }

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
