package compiler.negative

import compiler.reportings.DuplicateStructMemberReporting
import compiler.reportings.UnknownTypeReporting
import compiler.reportings.UnresolvableConstructorReporting
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
            .shouldReport<DuplicateStructMemberReporting> {
                it.duplicates should haveSize(2)
                it.duplicates.forAll {
                    it.name shouldBe "a"
                }
            }
    }

    "unknown declared member type" {
        validateModule("""
            struct X {
                a: Foo
            }
        """.trimIndent())
            .shouldReport<UnknownTypeReporting>()
    }

    "calling non-existent constructor" {
        validateModule("""
            struct X {
                a: Int
            }
            
            fun foo() {
                val x = X(true)
            }
        """.trimIndent())
            .shouldReport<UnresolvableConstructorReporting>()
    }
})