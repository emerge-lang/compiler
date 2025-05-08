package compiler.compiler.binding.type

import compiler.binding.type.BoundUnionTypeReference
import compiler.compiler.negative.validateModule
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class UnionTypeTests : FreeSpec({
    "simplification" - {
        val swCtx = validateModule("""
            interface T {}
            
            interface A {}
            interface B {}
        """.trimIndent())
            .first

        "read T & mut Any simplifies to mut T" {
            val type = swCtx.parseType("read T & mut Any")
            val simplified = type.shouldBeInstanceOf<BoundUnionTypeReference>().simplify()
            simplified.toString() shouldBe "mut testmodule.T"
        }

        "mut T? & read Any? simplifies to mut T?" {
            val type = swCtx.parseType("mut T? & read Any?")
            val simplified = type.shouldBeInstanceOf<BoundUnionTypeReference>().simplify()
            simplified.toString() shouldBe "mut testmodule.T?"
        }

        "read T? & mut Any simplifies to mut T" {
            val type = swCtx.parseType("read T? & mut Any")
            val simplified = type.shouldBeInstanceOf<BoundUnionTypeReference>().simplify()
            simplified.toString() shouldBe "mut testmodule.T"
        }
    }
})