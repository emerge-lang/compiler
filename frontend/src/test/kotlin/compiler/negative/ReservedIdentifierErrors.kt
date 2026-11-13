package compiler.compiler.negative

import compiler.diagnostic.ReservedIdentifierDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class ReservedIdentifierErrors : FreeSpec({
    "cannot declare" - {
        "a local variable" {
            validateModule("""
                fn test() {
                    __x = 3
                }
            """.trimIndent())
                .shouldFind<ReservedIdentifierDiagnostic> {
                    it.identifier shouldBe "__x"
                }
        }

        "a parameter" {
            validateModule("""
                fn test(__x: S32) {}
            """.trimIndent())
                .shouldFind<ReservedIdentifierDiagnostic>()
        }

        "a global variable" {
            validateModule("""
                __x: S32 = 3
            """.trimIndent())
                .shouldFind<ReservedIdentifierDiagnostic>()
        }

        "a function" {
            validateModule("""
                fn __test() {}
            """.trimIndent())
                .shouldFind<ReservedIdentifierDiagnostic>()
        }

        "a class" {
            validateModule("""
                class __Foo {}
            """.trimIndent())
                .shouldFind<ReservedIdentifierDiagnostic>()
        }

        "a member variable" {
            validateModule("""
                class Foo {
                    __x: S32 = 3
                }
            """.trimIndent())
                .shouldFind<ReservedIdentifierDiagnostic>()
        }

        "a type parameter of a function" {
            validateModule("""
                fn test<__T>(p: __T) {}
            """.trimIndent())
                .shouldFind<ReservedIdentifierDiagnostic>(allowMultiple = true)
        }

        "a type parameter of a class" {
            validateModule("""
                class Foo<__T> {}
            """.trimIndent())
                .shouldFind<ReservedIdentifierDiagnostic>()
        }

        "with a delimited identifier" {
            validateModule("""
                fn test() {
                    `__x` = 3
                }
            """.trimIndent())
                .shouldFind<ReservedIdentifierDiagnostic> {
                    it.identifier shouldBe "__x"
                }
        }
    }

    "cannot refer to the flag of a unique class" {
        validateModule("""
            unique class Usb {}
            fn test() {
                set __Usb_taken = false
            }
        """.trimIndent())
            .shouldFind<ReservedIdentifierDiagnostic> {
                it.identifier shouldBe "__Usb_taken"
            }
    }

    "cannot refer to the finalizer of a class" {
        validateModule("""
            class Foo {}
            fn test(foo: mut Foo) {
                foo.__Foo__finalize()
            }
        """.trimIndent())
            .ignore<compiler.diagnostic.UnresolvableFunctionOverloadDiagnostic>()
            .shouldFind<ReservedIdentifierDiagnostic>()
    }

    "identifiers that only contain __ are fine" {
        validateModule("""
            fn test() {
                a__b = 3
                _c = a__b
            }
        """.trimIndent()) should haveNoDiagnostics()
    }

    "the code the compiler generates may use the prefix" {
        validateModule("""
            import emerge.platform.World
            unique class Usb {
                n: S32 = init
            }
            fn test(world: mut World, arr: read Array<S32>) {
                Usb.take(world, 3)
                foreach x in arr {
                    y = x
                }
            }
        """.trimIndent()) should haveNoDiagnostics()
    }
})
