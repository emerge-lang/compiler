package compiler.compiler.negative

import compiler.diagnostic.OperatorNotDeclaredDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.diagnostic.VariableUsedAfterLifetimeDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class SlicingSyntaxTests : FreeSpec({
    "slicing syntax keeps the mutability of the source" - {
        "read" {
            validateModule("""
                fn test(p: read Array<S32>) -> read Array<S32> = p[1..<2]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "mut" {
            validateModule("""
                fn test(p: mut Array<S32>) -> mut Array<S32> = p[1..<2]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "const" {
            validateModule("""
                fn test(p: const Array<S32>) -> const Array<S32> = p[1..<2]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "exclusive" {
            validateModule("""
                fn test() -> exclusive Array<S32> {
                    a: exclusive _ = Array.new::<S32>(5, 0)
                    return a[1..<2]
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "cannot widen read to mut" {
            validateModule("""
                fn test(p: read Array<S32>) -> mut Array<S32> = p[1..<2]
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }
    }

    "slicing an exclusive array ends its lifetime" {
        validateModule("""
            fn test() -> exclusive Array<S32> {
                a: exclusive _ = Array.new::<S32>(5, 0)
                s = a[1..<2]
                return a
            }
        """.trimIndent())
            .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                it.variable.name.value shouldBe "a"
            }
    }

    "index types" - {
        "a literal index is an element" {
            validateModule("""
                fn test(p: read Array<S32>) -> S32 = p[0]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "a range value as the index is a slice" {
            validateModule("""
                fn test(p: read Array<S32>) -> read Array<S32> {
                    r = 1..<3
                    return p[r]
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "a parenthesised range literal is a slice" {
            validateModule("""
                fn test(p: read Array<S32>) -> read Array<S32> = p[(1..<3)]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "a slice is not an element" {
            validateModule("""
                fn test(p: read Array<S32>) -> S32 = p[1..<3]
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }
    }

    "ranges" - {
        "iterate as UWord" {
            validateModule("""
                fn test() {
                    foreach i in 0..<10 {
                        x: UWord = i
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "elements are not S32" {
            validateModule("""
                fn test() {
                    foreach i in 0..<10 {
                        x: S32 = i
                    }
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "a literal start takes the type of the end" {
            validateModule("""
                fn test(n: UWord) -> UWord = (0..<n).size
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "binds looser than arithmetic" {
            validateModule("""
                fn test(i: UWord, n: UWord) -> UWord {
                    r = i + 1..<n - 1
                    return r.size
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not declared for S32" {
            validateModule("""
                fn test(a: S32, b: S32) {
                    r = a..<b
                }
            """.trimIndent())
                .shouldFind<OperatorNotDeclaredDiagnostic>()
        }
    }
})
