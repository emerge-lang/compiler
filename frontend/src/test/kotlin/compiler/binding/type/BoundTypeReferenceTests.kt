package compiler.compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.validateModule
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class BoundTypeReferenceTests : FreeSpec({
    val ctx = validateModule("""
        class Box {
            var n: S32 = 0
        }
    """.trimIndent())
        .shouldHaveNoDiagnostics()
        .first

    assertSoftly = true
    "withMutabilityLimitedTo" - {
        "mut Array of" - {
            "mut" {
                val mutArrayOfMutString = ctx.parseType("mut Array<mut String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("mut Array<mut String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("mut Array<mut String>")
            }

            "read" {
                val mutArrayOfReadString = ctx.parseType("mut Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("mut Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("mut Array<read String>")
            }

            "const" {
                val mutArrayOfConstString = ctx.parseType("mut Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("mut Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("mut Array<const String>")
            }

            "exclusive" {
                val mutArrayOfExclString = ctx.parseType("mut Array<exclusive String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("mut Array<read String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("mut Array<read String>")
            }
        }

        "read Array of" - {
            "mut" {
                val mutArrayOfMutString = ctx.parseType("read Array<mut String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("read Array<mut String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("read Array<mut String>")
            }

            "read" {
                val mutArrayOfReadString = ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("read Array<read String>")
            }

            "const" {
                val mutArrayOfConstString = ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("read Array<const String>")
            }

            "exclusive" {
                val mutArrayOfExclString = ctx.parseType("read Array<exclusive String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("read Array<read String>")
            }
        }

        "const Array of" - {
            "mut" {
                val mutArrayOfMutString = ctx.parseType("const Array<mut String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("const Array<mut String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfMutString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("const Array<mut String>")
            }

            "read" {
                val mutArrayOfReadString = ctx.parseType("const Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfReadString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("const Array<read String>")
            }

            "const" {
                val mutArrayOfConstString = ctx.parseType("const Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("const Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("const Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("const Array<const String>")
                mutArrayOfConstString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("const Array<const String>")
            }

            "exclusive" {
                val mutArrayOfExclString = ctx.parseType("const Array<exclusive String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.MUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.READONLY) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfExclString.withMutabilityLimitedTo(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("const Array<read String>")
            }
        }

        "excl Array of" - {
            // no need to test because exclusive object members are not allowed
        }
    }
})