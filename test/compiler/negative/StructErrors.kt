package matchers.compiler.negative

import compiler.reportings.DuplicateStructMemberReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forAll
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class StructErrors : FreeSpec({
    "duplicate member" {
        validateModule("""
            struct X {
                a: Int
                b: Int
                a: Boolean
            }
        """.trimIndent())
            .shouldRejectWith<DuplicateStructMemberReporting> {
                it.duplicates should haveSize(2)
                it.duplicates.forAll {
                    it.name shouldBe "a"
                }
            }
    }
})