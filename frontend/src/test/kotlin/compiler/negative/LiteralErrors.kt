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

        "integer literal out of range - expecting S8" {
            validateModule("""
                x: S8 = 200
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe s8
                }
        }

        "integer literal out of range - expecting S32" {
            validateModule("""
                x: S32 = 100000000000000
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe s32
                }
        }

        "integer literal out of range - expecting SWord" {
            validateModule("""
                x: SWord = 2147483649
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe sword
                }
        }

        "integer literal out of range - expecting UWord" {
            validateModule("""
                x: UWord = 4294967298
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe uword
                }
        }
    }
})