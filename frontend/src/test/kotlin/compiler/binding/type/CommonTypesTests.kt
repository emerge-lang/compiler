package compiler.compiler.binding.type

import compiler.binding.type.BoundIntersectionTypeReference.Companion.intersect
import compiler.binding.type.BoundTypeReference
import compiler.compiler.negative.validateModule
import compiler.lexer.Span
import io.kotest.assertions.withClue
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty

/**
 * What the proofs conjecture of [BoundTypeReference.intersect] and [BoundTypeReference.closestCommonSupertypeWith]
 * (`intersect_is_below_both`, `closest_common_supertype_is_above_both` in `type-system-proofs/theories/Conjectures.v`),
 * checked for every pair of a set of types of the fragment the proofs cover.
 */
class CommonTypesTests : FreeSpec({
    val swCtx = validateModule("""
        interface A {}
        interface B {}
        interface C : A {}
        class Box<E> {}
        class Ctx<P, Q : A, R : A?> {}
    """.trimIndent()).first

    val types = listOf(
        "A", "mut A", "const A", "exclusive A", "A?", "mut A?",
        "B", "const B?",
        "C", "mut C", "exclusive C?",
        "Any", "Any?", "mut Any", "exclusive Nothing", "exclusive Nothing?",
        "Box<A>", "Box<C>", "Box<in A>", "Box<out A>", "Box<in C>", "Box<out C>", "Box<mut A>", "Box<A?>", "mut Box<out A>?",
        "P", "P?", "mut P", "Q", "const Q", "Q?", "R", "R!", "R?", "Box<P>", "Box<out Q>", "Box<R!>",
        "A & B", "mut A & B", "A? & B?", "C & Q", "Q & B",
    ).map { it to swCtx.parseTypeIn("Ctx", it) }

    fun BoundTypeReference.isBelow(other: BoundTypeReference) = evaluateAssignabilityTo(other, Span.UNKNOWN) == null

    fun violationsOf(check: (BoundTypeReference, BoundTypeReference) -> String?): List<String> = types.flatMap { (aStr, a) ->
        types.mapNotNull { (bStr, b) ->
            try {
                check(a, b)?.let { "$aStr, $bStr: $it" }
            } catch (e: Exception) {
                "$aStr, $bStr: ${e::class.simpleName} ${e.message}"
            }
        }
    }

    "the closest common supertype is above both types" {
        val violations = violationsOf { a, b ->
            val supertype = a.closestCommonSupertypeWith(b)
            supertype.takeUnless { a.isBelow(it) && b.isBelow(it) }?.toString()
        }
        withClue(violations.joinToString("\n")) {
            violations.shouldBeEmpty()
        }
    }

    "the intersection is below both types" {
        val violations = violationsOf { a, b ->
            val intersection = a.intersect(b)
            intersection.takeUnless { it.isBelow(a) && it.isBelow(b) }?.toString()
        }
        withClue(violations.joinToString("\n")) {
            violations.shouldBeEmpty()
        }
    }

    // the type parameters of Ctx, bound in ways that tell their mutability and nullability apart
    val instantiations = listOf(
        "Ctx<mut A, mut C, A?>",
        "Ctx<const A, C, mut C>",
        "Ctx<A?, const A, const C?>",
        "Ctx<exclusive C, exclusive C, exclusive Nothing?>",
        "Ctx<mut Box<A>?, mut A, mut A?>",
    ).map { it to swCtx.parseType(it).inherentTypeBindings }

    "the instance of the intersection is below the instances of both types" {
        val violations = instantiations.flatMap { (ctxStr, bindings) ->
            violationsOf { a, b ->
                val intersection = a.intersect(b).instantiateAllParameters(bindings)
                val aInstance = a.instantiateAllParameters(bindings)
                val bInstance = b.instantiateAllParameters(bindings)
                intersection
                    .takeUnless { it.isBelow(aInstance) && it.isBelow(bInstance) }
                    ?.let { "in $ctxStr: $it, of $aInstance and $bInstance" }
            }
        }
        withClue(violations.joinToString("\n")) {
            violations.shouldBeEmpty()
        }
    }
})
