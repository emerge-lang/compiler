package compiler.compiler.negative

import compiler.reportings.IntegerLiteralOutOfRangeReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class LiteralErrors : FreeSpec({
    "integers" - {
        "integer literal out of range - no expected type" {
            validateModule("""
                x = 100000000000000
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe s32
                }
        }

        "integer literal out of range - expecting byte" {
            validateModule("""
                x: Byte = 200
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe s8
                }
        }

        "integer literal out of range - expecting int" {
            validateModule("""
                x: S32 = 100000000000000
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe s32
                }
        }

        "integer literal out of range - expecting iword" {
            validateModule("""
                x: iword = 2147483649
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe sword
                }
        }

        "integer literal out of range - expecting uword" {
            validateModule("""
                x: uword = 4294967298
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe uword
                }
        }
    }
})