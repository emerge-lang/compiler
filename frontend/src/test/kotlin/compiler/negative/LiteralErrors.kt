package compiler.compiler.negative

import compiler.binding.type.BuiltinByte
import compiler.binding.type.BuiltinInt
import compiler.binding.type.BuiltinSignedWord
import compiler.binding.type.BuiltinUnsignedWord
import compiler.reportings.IntegerLiteralOutOfRangeReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class LiteralErrors : FreeSpec({
    "integers" - {
        "integer literal out of range - no expected type" {
            validateModule("""
                val x = 100000000000000
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe BuiltinInt
                }
        }

        "integer literal out of range - expecting byte" {
            validateModule("""
                val x: Byte = 200
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe BuiltinByte
                }
        }

        "integer literal out of range - expecting int" {
            validateModule("""
                val x: Int = 100000000000000
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe BuiltinInt
                }
        }

        "integer literal out of range - expecting iword" {
            validateModule("""
                val x: iword = 2147483649
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe BuiltinSignedWord
                }
        }

        "integer literal out of range - expecting uword" {
            validateModule("""
                val x: uword = 4294967298
            """.trimIndent())
                .shouldReport<IntegerLiteralOutOfRangeReporting> {
                    it.expectedType shouldBe BuiltinUnsignedWord
                }
        }
    }
})