package compiler.compiler.binding.type

import compiler.binding.type.BoundIntersectionTypeReference
import compiler.compiler.negative.validateModule
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class IntersectionTypeTests : FreeSpec({
    val swCtx = validateModule("""
            interface T {}
            
            interface A {}
            interface B {}
            interface C {}
        """.trimIndent())
        .first

    "simplification" - {
        "read T & mut Any simplifies to mut T" {
            val type = swCtx.parseType("read T & mut Any")
            val simplified = type.shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
            simplified.toString() shouldBe "mut testmodule.T"
        }

        "mut T? & read Any? simplifies to mut T?" {
            val type = swCtx.parseType("mut T? & read Any?")
            val simplified = type.shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
            simplified.toString() shouldBe "mut testmodule.T?"
        }

        "read T? & mut Any simplifies to mut T" {
            val type = swCtx.parseType("read T? & mut Any")
            val simplified = type.shouldBeInstanceOf<BoundIntersectionTypeReference>().simplify()
            simplified.toString() shouldBe "mut testmodule.T"
        }
    }

    "subtyping" - {
        "non-compound target" {
            swCtx.parseType("A & B") should beAssignableTo(swCtx.parseType("A"))
            swCtx.parseType("A & B") should beAssignableTo(swCtx.parseType("B"))
        }

        "compound target" {
            swCtx.parseType("A & B & C") should beAssignableTo(swCtx.parseType("A & B"))
            swCtx.parseType("A & B & C") should beAssignableTo(swCtx.parseType("A & C"))
            swCtx.parseType("A & B & C") should beAssignableTo(swCtx.parseType("B & C"))
        }
    }
})