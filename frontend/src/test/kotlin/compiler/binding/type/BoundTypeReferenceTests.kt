package compiler.compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.SoftwareContext
import compiler.binding.type.BoundTypeReference
import compiler.compiler.negative.lexCode
import compiler.compiler.negative.shouldHaveNoDiagnostics
import compiler.compiler.negative.validateModule
import compiler.parser.grammar.rule.MatchingResult
import io.github.tmarsteel.emerge.common.CanonicalElementName
import io.kotest.assertions.fail
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import compiler.parser.grammar.Type as TypeGrammar

class BoundTypeReferenceTests : FreeSpec({
    val ctx = validateModule("""
        class Box {
            var n: S32 = 0
        }
    """.trimIndent())
        .shouldHaveNoDiagnostics()
        .first

    assertSoftly = true
    "withLimitedMutability" - {
        "mut Array of" - {
            "mut" {
                val mutArrayOfMutString = ctx.parseType("mut Array<mut String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("mut Array<mut String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("mut Array<mut String>")
            }

            "read" {
                val mutArrayOfReadString = ctx.parseType("mut Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("mut Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("mut Array<read String>")
            }

            "const" {
                val mutArrayOfConstString = ctx.parseType("mut Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("mut Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("mut Array<const String>")
            }

            "exclusive" {
                val mutArrayOfExclString = ctx.parseType("mut Array<exclusive String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("mut Array<read String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("mut Array<read String>")
            }
        }

        "read Array of" - {
            "mut" {
                val mutArrayOfMutString = ctx.parseType("read Array<mut String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("read Array<mut String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("read Array<mut String>")
            }

            "read" {
                val mutArrayOfReadString = ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("read Array<read String>")
            }

            "const" {
                val mutArrayOfConstString = ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("read Array<const String>")
            }

            "exclusive" {
                val mutArrayOfExclString = ctx.parseType("read Array<exclusive String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("read Array<read String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("read Array<read String>")
            }
        }

        "const Array of" - {
            "mut" {
                val mutArrayOfMutString = ctx.parseType("const Array<mut String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("const Array<mut String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfMutString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("const Array<mut String>")
            }

            "read" {
                val mutArrayOfReadString = ctx.parseType("const Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfReadString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("const Array<read String>")
            }

            "const" {
                val mutArrayOfConstString = ctx.parseType("const Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("const Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("const Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("const Array<const String>")
                mutArrayOfConstString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("const Array<const String>")
            }

            "exclusive" {
                val mutArrayOfExclString = ctx.parseType("const Array<exclusive String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.MUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.READONLY) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.IMMUTABLE) shouldBe ctx.parseType("const Array<read String>")
                mutArrayOfExclString.withLimitedMutability(TypeMutability.EXCLUSIVE) shouldBe ctx.parseType("const Array<read String>")
            }
        }

        "excl Array of" - {
            // no need to test because exclusive object members are not allowed
        }
    }
})

private fun SoftwareContext.parseType(
    type: String,
    module: String = "testmodule",
    definedAt: StackTraceElement = Thread.currentThread().stackTrace[2]
): BoundTypeReference {
    val moduleCtx = getRegisteredModule(CanonicalElementName.Package(listOf(module)))
    val tokens = lexCode(addPackageDeclaration = false, code = type, invokedFrom = definedAt)
    val typeMatch = TypeGrammar.match(tokens, 0)
        .sortedByDescending { it is MatchingResult.Success<*> }
        .filter { when (it) {
            is MatchingResult.Success<*> -> it.continueAtIndex == tokens.size - 1
            else -> true
        } }
        .firstOrNull()
    if (typeMatch == null) {
        fail("Failed to parse type")
    }
    if (typeMatch is MatchingResult.Error) {
        fail(typeMatch.diagnostic.toString())
    }
    check(typeMatch is MatchingResult.Success<TypeReference>)
    val boundType = moduleCtx.sourceFiles.first().context.resolveType(typeMatch.item)
    return boundType
}