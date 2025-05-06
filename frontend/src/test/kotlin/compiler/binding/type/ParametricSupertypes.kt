package compiler.compiler.binding.type

import compiler.binding.type.RootResolvedTypeReference
import compiler.compiler.negative.validateModule
import compiler.util.twoElementPermutationsUnordered
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class ParametricSupertypes : FreeSpec({
    "closest common supertype" - {
        "same basetype in param" - {
            val swCtx = validateModule("""
                interface SomeT {}
            """.trimIndent(), noStd = true).first
            val types = listOf(
                swCtx.parseType("exclusive Array<mut SomeT>") as RootResolvedTypeReference,
                swCtx.parseType("exclusive Array<read SomeT>") as RootResolvedTypeReference,
                swCtx.parseType("exclusive Array<const SomeT>") as RootResolvedTypeReference,
            )
            for ((typeA, typeB) in types.twoElementPermutationsUnordered()) {
                val aArgMut = typeA.arguments!!.single().mutability
                val bArgMut = typeB.arguments!!.single().mutability
                val expectedArgMutability = aArgMut.intersect(bArgMut)
                val expectedType = swCtx.parseType("exclusive Array<${expectedArgMutability.keyword.text} SomeT>")

                "${aArgMut.keyword.text} x ${bArgMut.keyword.text} -> ${expectedArgMutability.keyword.text}" {
                    typeA.closestCommonSupertypeWith(typeB) shouldBe expectedType
                    typeB.closestCommonSupertypeWith(typeA) shouldBe expectedType
                }
            }
        }
    }
})