package compiler.compiler.negative

import compiler.reportings.ImpureInvocationInPureContextReporting
import compiler.reportings.ModifyingInvocationInReadonlyContextReporting
import compiler.reportings.ReadInPureContextReporting
import compiler.reportings.StateModificationOutsideOfPurityBoundaryReporting
import io.kotest.core.spec.style.FreeSpec

class PurityErrors : FreeSpec({
    "reading compile-time constant globals is okay from a pure context" {
        validateModule("""
            fun computeSomething(y: Int) -> Int {
                return y
            }
            x = computeSomething(2)
            fun test() -> Int {
                return x
            }
        """.trimIndent()).shouldHaveNoDiagnostics()
    }

    "reading runtime-dependent final globals is not okay in a pure context" {
        validateModule("""
            intrinsic readonly fun readRuntimeState() -> Int
            x = readRuntimeState()
            fun test() -> Int {
                return x
            }
        """.trimIndent())
            .shouldReport<ReadInPureContextReporting>()
    }

    "calling a readonly function from a pure context" {
        validateModule("""
            var x = 1
            readonly fun a() {
                y = x + 1
            }
            fun b() {
                a()
            }
        """.trimIndent())
            .shouldReport<ImpureInvocationInPureContextReporting>()
    }

    "calling a modifying function from a pure context" {
        validateModule("""
            var x = 1
            mutable fun a() {
                set x = 2
            }
            pure fun b() {
                a()
            }
        """.trimIndent())
            .shouldReport<ImpureInvocationInPureContextReporting>()
    }

    "calling a modifying function from a readonly context" {
        validateModule("""
            var x = 1
            mutable fun a() {
                set x = 2
            }
            readonly fun b() {
                a()
            }
        """.trimIndent())
            .shouldReport<ModifyingInvocationInReadonlyContextReporting>()
    }

    "reading from outside a pure context" {
        validateModule("""
            var x = 1
            pure fun a() {
                x
            }
        """.trimIndent())
            .shouldReport<ReadInPureContextReporting>()
    }

    "mutating outside of a pure context" {
        validateModule("""
            var x = 1
            pure fun a() {
                set x = 2
            }
        """.trimIndent())
            .shouldReport<StateModificationOutsideOfPurityBoundaryReporting>()
    }

    "mutation outside of a readonly context" {
        validateModule("""
            var x = 1
            readonly fun a() {
                set x = 2
            }
        """.trimIndent())
            .shouldReport<StateModificationOutsideOfPurityBoundaryReporting>()
    }
})