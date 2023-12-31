package compiler.negative

import compiler.reportings.DuplicateStructMemberReporting
import compiler.reportings.UnknownTypeReporting
import compiler.reportings.ValueNotAssignableReporting
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

    "calling a constructor with incorrect argument types" {
        validateModule("""
            struct X {
                a: Int
            }
            
            fun foo() {
                val x = X(true)
            }
        """.trimIndent())
            .shouldReport<ValueNotAssignableReporting>()
    }

    "calling a hypothetical constructor of a non-existent type" {
        validateModule("""
            val x = Nonexistent()
        """.trimIndent())
    }

    "generics" - {
        "type parameter with unresolvable bound" {
            validateModule("""
                struct X<T : Bla> {}
            """.trimIndent())
                .shouldReport<UnknownTypeReporting> {
                    it.erroneousReference.simpleName shouldBe "Bla"
                }
        }
    }
})