package compiler.compiler.negative

import compiler.reportings.AssignmentOutsideOfPurityBoundaryReporting
import compiler.reportings.ImpureInvocationInPureContextReporting
import compiler.reportings.ModifyingInvocationInReadonlyContextReporting
import compiler.reportings.MutableUsageOfStateOutsideOfPurityBoundaryReporting
import compiler.reportings.ReadInPureContextReporting
import io.kotest.core.spec.style.FreeSpec

class PurityErrors : FreeSpec({
    "reading compile-time constant globals is okay from a pure context" {
        validateModule("""
            fn computeSomething(y: S32) -> S32 {
                return y
            }
            x = computeSomething(2)
            fn test() -> S32 {
                return x
            }
        """.trimIndent()).shouldHaveNoDiagnostics()
    }

    "reading runtime-dependent final globals is not okay in a pure context" {
        validateModule("""
            intrinsic read fn readRuntimeState() -> S32
            x = readRuntimeState()
            fn test() -> S32 {
                return x
            }
        """.trimIndent())
            .shouldReport<ReadInPureContextReporting>()
    }

    "calling a read function from a pure context" {
        validateModule("""
            var x = 1
            read fn a() {
                y = x + 1
            }
            fn b() {
                a()
            }
        """.trimIndent())
            .shouldReport<ImpureInvocationInPureContextReporting>()
    }

    "calling a modifying function from a pure context" {
        validateModule("""
            var x = 1
            mut fn a() {
                set x = 2
            }
            pure fn b() {
                a()
            }
        """.trimIndent())
            .shouldReport<ImpureInvocationInPureContextReporting>()
    }

    "calling a modifying function from a read context" {
        validateModule("""
            var x = 1
            mut fn a() {
                set x = 2
            }
            read fn b() {
                a()
            }
        """.trimIndent())
            .shouldReport<ModifyingInvocationInReadonlyContextReporting>()
    }

    "reading from outside a pure context" {
        validateModule("""
            var x = 1
            pure fn a() {
                x
            }
        """.trimIndent())
            .shouldReport<ReadInPureContextReporting>()
    }

    "mutating outside of a pure context" - {
        "by variable assignment" {
            validateModule("""
                var x = 1
                pure fn a() {
                    set x = 2
                }
            """.trimIndent())
                .shouldReport<AssignmentOutsideOfPurityBoundaryReporting>()
        }

        "by calling a function that takes a mutable parameter" {
            validateModule("""
                class H {
                    var i = 0
                }
                var x = H()
                fn pureMutate(p: mut H) {
                    set p.i = 1
                }
                read fn test() {
                    pureMutate(x)
                }
            """.trimIndent())
                .shouldReport<MutableUsageOfStateOutsideOfPurityBoundaryReporting>()
        }
    }

    "mutation outside of a read context" {
        validateModule("""
            var x = 1
            read fn a() {
                set x = 2
            }
        """.trimIndent())
            .shouldReport<AssignmentOutsideOfPurityBoundaryReporting>()
    }
})