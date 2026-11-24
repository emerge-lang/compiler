package compiler.compiler.negative

import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.SuperfluousSafeObjectTraversal
import compiler.diagnostic.UnsafeObjectTraversalDiagnostic
import io.kotest.core.spec.style.FreeSpec

class NullSafeInvocationTests : FreeSpec({
    val declarations = """
        class X {
            get fn f(self) -> S32 = 0
            fn member(self) -> S32 = 1
        }
        intrinsic fn provide() -> X?
        intrinsic fn consume(self: X)
        intrinsic fn combine(self: X, other: S32) -> S32
    """.trimIndent()

    "on a nullable receiver" - {
        "top-level function as a statement" {
            validateModule("""
                $declarations
                fn test() {
                    x = provide()
                    x?.consume()
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "member function as a statement" {
            validateModule("""
                $declarations
                fn test(x: X?) {
                    x?.member()
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "on the result of an invocation" {
            validateModule("""
                $declarations
                fn test() {
                    provide()?.consume()
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "evaluates to a nullable type" {
            validateModule("""
                $declarations
                fn test(x: X?) -> S32? = x?.member()
            """.trimIndent())
                .shouldHaveNoDiagnostics()

            validateModule("""
                $declarations
                fn test(x: X?) -> S32 = x?.member()
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }

        "chained" {
            validateModule("""
                $declarations
                class Y {
                    fn x(self) -> X? = provide()
                }
                fn test(y: Y?) -> S32? = y?.x()?.member()
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "getter" {
            validateModule("""
                $declarations
                fn test(x: X?) -> S32? = x?.f
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "the receiver is not null in the arguments" {
            validateModule("""
                $declarations
                fn test(x: X?) -> S32? = x?.combine(x.f)
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "the receiver may still be null after the invocation" {
            validateModule("""
                $declarations
                fn test(x: X?) -> S32 {
                    x?.consume()
                    return x.f
                }
            """.trimIndent())
                .shouldFind<UnsafeObjectTraversalDiagnostic>()
        }
    }

    "on a non-nullable receiver is superfluous" - {
        "function" {
            validateModule("""
                $declarations
                fn test(x: X) {
                    x?.consume()
                }
            """.trimIndent())
                .shouldFind<SuperfluousSafeObjectTraversal>()
        }

        "getter, reported only once" {
            validateModule("""
                $declarations
                fn test(x: X) -> S32 = x?.f
            """.trimIndent())
                .shouldFind<SuperfluousSafeObjectTraversal>()
        }
    }

    "member assignment" - {
        val assignmentDeclarations = """
            class Y {
                var a: S32 = 0
                set fn b(self: mut _, v: S32) {}
            }
        """.trimIndent()

        "to a member variable of a nullable object" {
            validateModule("""
                $assignmentDeclarations
                fn test(y: mut Y?) {
                    set y?.a = 3
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "through a setter of a nullable object" {
            validateModule("""
                $assignmentDeclarations
                fn test(y: mut Y?) {
                    set y?.b = 3
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "the object is not null in the value" {
            validateModule("""
                $assignmentDeclarations
                fn test(y: mut Y?) {
                    set y?.a = y.a + 1
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "the object may still be null after the assignment" {
            validateModule("""
                $assignmentDeclarations
                fn test(y: mut Y?) -> S32 {
                    set y?.a = 3
                    return y.a
                }
            """.trimIndent())
                .shouldFind<UnsafeObjectTraversalDiagnostic>()
        }

        "without ?. on a nullable object" {
            validateModule("""
                $assignmentDeclarations
                fn test(y: mut Y?) {
                    set y.a = 3
                }
            """.trimIndent())
                .shouldFind<UnsafeObjectTraversalDiagnostic>()
        }

        "superfluous on a non-nullable object, reported only once" - {
            "member variable" {
                validateModule("""
                    $assignmentDeclarations
                    fn test(y: mut Y) {
                        set y?.a = 3
                    }
                """.trimIndent())
                    .shouldFind<SuperfluousSafeObjectTraversal>()
            }

            "setter" {
                validateModule("""
                    $assignmentDeclarations
                    fn test(y: mut Y) {
                        set y?.b = 3
                    }
                """.trimIndent())
                    .shouldFind<SuperfluousSafeObjectTraversal>()
            }
        }
    }
})
