package compiler.compiler.negative

import compiler.diagnostic.IndexedLengthOutsideIndexDiagnostic
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

        // a type parameter is never bound to an own type, so the slice of an own array is mut, not
        // own; see roadmap item 19
        "own gives mut" {
            validateModule("""
                fn test() -> mut Array<S32> {
                    a: own _ = Array.new::<S32>(5, 0)
                    return a[1..<2]
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "own does not stay own" {
            validateModule("""
                fn test() -> own Array<S32> {
                    a: own _ = Array.new::<S32>(5, 0)
                    return a[1..<2]
                }
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }

        "cannot widen read to mut" {
            validateModule("""
                fn test(p: read Array<S32>) -> mut Array<S32> = p[1..<2]
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }
    }

    "slicing an own array ends its lifetime" {
        validateModule("""
            fn test() -> own Array<S32> {
                a: own _ = Array.new::<S32>(5, 0)
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

    "indexed length" - {
        "last element" {
            validateModule("""
                fn test(p: read Array<S32>) -> S32 = p[$ - 1]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "in a slice" {
            validateModule("""
                fn test(p: read Array<S32>) -> read Array<S32> = p[0..<$ - 3]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "refers to the innermost index access" {
            validateModule("""
                fn test(a: read Array<S32>, b: read Array<UWord>) -> S32 = a[b[$ - 1]]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "after a nested index access refers to the outer one again" {
            validateModule("""
                fn test(a: read Array<S32>, b: read Array<UWord>) -> S32 = a[b[0] + $ - 1]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "on the result of an invocation" {
            validateModule("""
                fn make() -> own Array<S32> = Array.new::<S32>(3, 0)
                fn test() -> S32 = make()[$ - 1]
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "with an operand that is computed from a range" {
            validateModule("""
                fn test(n: UWord) -> read Array<S32> {
                    a: own _ = Array.new::<S32>(n, 0)
                    return a[(0..<n).size - 1..<$]
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "in the index of an index assignment" {
            validateModule("""
                fn test(p: mut Array<S32>) {
                    set p[$ - 1] = 5
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not in the value of an index assignment" {
            validateModule("""
                fn test(p: mut Array<UWord>) {
                    set p[0] = $
                }
            """.trimIndent())
                .shouldFind<IndexedLengthOutsideIndexDiagnostic>()
        }

        "not outside of an index access" {
            validateModule("""
                fn test() -> UWord = $
            """.trimIndent())
                .shouldFind<IndexedLengthOutsideIndexDiagnostic>()
        }

        "not after an index access" {
            validateModule("""
                fn id(x: UWord) -> UWord = x
                fn test(p: read Array<S32>) -> UWord {
                    x = p[0]
                    return id($)
                }
            """.trimIndent())
                .shouldFind<IndexedLengthOutsideIndexDiagnostic>()
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
