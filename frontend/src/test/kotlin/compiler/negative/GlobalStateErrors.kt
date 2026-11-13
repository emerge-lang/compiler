package compiler.compiler.negative

import compiler.diagnostic.MutableGlobalVariableDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.assertions.throwables.shouldThrow
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.string.shouldContain

/**
 * There is no state that every function can reach: top-level variables are constants, and functions have no
 * effect modifiers. What a function can read and change is what its parameters give it.
 */
class GlobalStateErrors : FreeSpec({
    "top-level variables are constants" - {
        "a constant can be read from any function" {
            validateModule("""
                class Config {
                    retries: S32 = init
                }
                LIMIT: S32 = 3
                NAMES: Array<String> = ["a", "b"]
                DEFAULTS: const Config = Config(computeRetries())
                fn computeRetries() -> S32 = LIMIT + 1
                fn test() -> S32 = LIMIT + DEFAULTS.retries
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "it cannot be re-assignable" {
            validateModule("""
                var counter: S32 = 0
            """.trimIndent())
                .shouldFind<MutableGlobalVariableDiagnostic> {
                    it.message shouldContain "re-assignable"
                }
        }

        "it cannot be of a mut type" {
            validateModule("""
                class Box {
                    var n: S32 = 0
                }
                shared: mut Box = Box()
            """.trimIndent())
                .shouldFind<MutableGlobalVariableDiagnostic> {
                    it.message shouldContain "mut testmodule.Box"
                }
        }

        "it cannot be of a read type" {
            validateModule("""
                class Box {
                    var n: S32 = 0
                }
                shared: read Box = Box()
            """.trimIndent())
                .shouldFind<MutableGlobalVariableDiagnostic>()
        }

        "it cannot hold something mutable in a type argument" {
            validateModule("""
                class Box {
                    var n: S32 = 0
                }
                class Holder<T> {
                    value: T = init
                }
                shared: const Holder<mut Box> = Holder(Box())
            """.trimIndent())
                .shouldFind<MutableGlobalVariableDiagnostic>()
        }

        "it cannot be a token" {
            validateModule("""
                token class Counter {
                    var n: S32 = 0
                }
                shared: read Counter = Counter()
            """.trimIndent())
                .shouldFind<MutableGlobalVariableDiagnostic>()
        }
    }

    "functions have no effect modifiers" - {
        "mut, read and pure are not accepted on a function" {
            for (modifier in listOf("mut", "read", "pure")) {
                shouldThrow<AssertionError> {
                    validateModule("""
                        ${'$'}modifier fn test() {}
                    """.trimIndent())
                }.message!! shouldContain "Failed to parse"
            }
        }

        "pure is usable as a name" {
            validateModule("""
                fn test(pure: S32) -> S32 = pure
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "a function changes state through a parameter" {
            validateModule("""
                token class Counter {
                    var n: S32 = 0
                }
                fn increment(borrow counter: mut Counter) {
                    set counter.n = counter.n + 1
                }
                fn current(borrow counter: read Counter) -> S32 = counter.n
                fn test(borrow counter: mut Counter) -> S32 {
                    increment(counter)
                    return current(counter)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "a function cannot change state it was given as read" {
            validateModule("""
                token class Counter {
                    var n: S32 = 0
                }
                fn increment(borrow counter: mut Counter) {
                    set counter.n = counter.n + 1
                }
                fn test(borrow counter: read Counter) {
                    increment(counter)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }
    }

    "object traversal limits mutability" - {
        // own mutability on object members is currently not allowed, so no need to test

        "member declared mut, accessed through read reference to the object - mutability becomes read" {
            validateModule("""
                class Box {
                    var n: S32 = 0
                }
                class Holder {
                    box: mut Box = Box()
                }
                fn test(p: read Holder) {
                    v: mut Box
                    set v = p.box                
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "read testmodule.Box"
                    it.targetType.toString() shouldBe "mut testmodule.Box"
                }
        }

        "member declared mut, accessed through const reference to the object - mutability becomes read" {
            validateModule("""
                class Box {
                    var n: S32 = 0
                }
                class Holder {
                    box: mut Box = Box()
                }
                fn test(p: const Holder) {
                    v: mut Box
                    set v = p.box   
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "read testmodule.Box"
                    it.targetType.toString() shouldBe "mut testmodule.Box"
                }
        }

        "member declared const, accessed through mut reference to the object - mutability stays const" {
            validateModule("""
                class Box {
                    var n: S32 = 0
                }
                class Holder {
                    box: const Box = Box()
                }
                fn test(p: mut Holder) -> const Box = p.box
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }
})