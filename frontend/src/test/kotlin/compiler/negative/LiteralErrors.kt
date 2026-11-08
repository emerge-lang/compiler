package compiler.compiler.negative

import compiler.diagnostic.IntegerLiteralOutOfRangeDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class LiteralErrors : FreeSpec({
    "integers" - {
        "integer literal out of range - no expected type" {
            validateModule("""
                x = 100000000000000
            """.trimIndent())
                .shouldFind<IntegerLiteralOutOfRangeDiagnostic> {
                    it.expectedType shouldBe s32
                }
        }

        "integer literal out of range - expecting S8" {
            validateModule("""
                x: S8 = 200
            """.trimIndent())
                .shouldFind<IntegerLiteralOutOfRangeDiagnostic> {
                    it.expectedType shouldBe s8
                }
        }

        "integer literal out of range - expecting S32" {
            validateModule("""
                x: S32 = 100000000000000
            """.trimIndent())
                .shouldFind<IntegerLiteralOutOfRangeDiagnostic> {
                    it.expectedType shouldBe s32
                }
        }

        "integer literal out of range - expecting SWord" {
            validateModule("""
                x: SWord = 2147483649
            """.trimIndent())
                .shouldFind<IntegerLiteralOutOfRangeDiagnostic> {
                    it.expectedType shouldBe sword
                }
        }

        "integer literal out of range - expecting UWord" {
            validateModule("""
                x: UWord = 4294967298
            """.trimIndent())
                .shouldFind<IntegerLiteralOutOfRangeDiagnostic> {
                    it.expectedType shouldBe uword
                }
        }
    }

    "negative literals" - {
        "fitting S8" {
            validateModule("""
                a: S8 = -128
                b: S8 = -0x80
                c: S32 = 3-1
                d: F32 = -1.5
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "out of range for S8" {
            validateModule("""
                x: S8 = -129
            """.trimIndent())
                .shouldFind<IntegerLiteralOutOfRangeDiagnostic> {
                    it.expectedType shouldBe s8
                }
        }

        "parenthesised literal is not folded" {
            validateModule("""
                x: S8 = -(128)
            """.trimIndent())
                .shouldFind<IntegerLiteralOutOfRangeDiagnostic> {
                    it.expectedType shouldBe s8
                }
        }
    }
})
