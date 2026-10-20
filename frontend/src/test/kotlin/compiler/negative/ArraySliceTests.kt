package compiler.compiler.negative

import compiler.diagnostic.BorrowedVariableCapturedDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.VariableUsedAfterLifetimeDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class ArraySliceTests : FreeSpec({
    "slice keeps the mutability of the source" - {
        "read" {
            validateModule("""
                fn test(p: read Array<S32>) -> read Array<S32> = p.slice(1, 2)
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "mut" {
            validateModule("""
                fn test(p: mut Array<S32>) -> mut Array<S32> = p.slice(1, 2)
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "const" {
            validateModule("""
                fn test(p: const Array<S32>) -> const Array<S32> = p.slice(1, 2)
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "exclusive" {
            validateModule("""
                fn test() -> exclusive Array<S32> {
                    a: exclusive _ = Array.new::<S32>(5, 0)
                    return a.slice(1, 2)
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "variant element types" {
            validateModule("""
                fn test(p: mut Array<out S32>) -> mut Array<out S32> = p.sliceOrPanic(1, 2)
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }

    "slice cannot widen the mutability" - {
        "read to mut" {
            validateModule("""
                fn test(p: read Array<S32>) -> mut Array<S32> = p.slice(1, 2)
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }

        "mut to const" {
            validateModule("""
                fn test(p: mut Array<S32>) -> const Array<S32> = p.slice(1, 2)
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }

        "element type" {
            validateModule("""
                fn test(p: read Array<out S32>) -> read Array<S32> = p.slice(1, 2)
            """.trimIndent())
                .shouldFind<ReturnTypeMismatchDiagnostic>()
        }
    }

    "slicing an exclusive array ends its lifetime" {
        validateModule("""
            fn test() -> exclusive Array<S32> {
                a: exclusive _ = Array.new::<S32>(5, 0)
                s = a.slice(1, 2)
                return a
            }
        """.trimIndent())
            .shouldFind<VariableUsedAfterLifetimeDiagnostic> {
                it.variable.name.value shouldBe "a"
            }
    }

    "slicing a borrowed array is a capture" {
        validateModule("""
            fn test(borrow p: read Array<S32>) -> UWord {
                s = p.slice(1, 2)
                return p.size + s.size
            }
        """.trimIndent())
            .shouldFind<BorrowedVariableCapturedDiagnostic>()
    }

    "slicing an owned read array keeps it usable" {
        validateModule("""
            fn test(p: read Array<S32>) -> UWord {
                s = p.slice(1, 2)
                return p.size + s.size
            }
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }
})
