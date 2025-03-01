package compiler.compiler.negative

import compiler.diagnostic.AssignmentOutsideOfPurityBoundaryDiagnostic
import compiler.diagnostic.ImpureInvocationInPureContextDiagnostic
import compiler.diagnostic.ModifyingInvocationInReadonlyContextDiagnostic
import compiler.diagnostic.MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic
import compiler.diagnostic.ReadInPureContextDiagnostic
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
            .shouldReport<ReadInPureContextDiagnostic>()
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
            .shouldReport<ImpureInvocationInPureContextDiagnostic>()
    }

    "calling a modifying function from a pure context" {
        validateModule("""
            var x = 1
            mut fn a() {
                set x = 2
            }
            fn b() {
                a()
            }
        """.trimIndent())
            .shouldReport<ModifyingInvocationInReadonlyContextDiagnostic>()
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
            .shouldReport<ModifyingInvocationInReadonlyContextDiagnostic>()
    }

    "reading from outside a pure context" {
        validateModule("""
            var x = 1
            pure fn a() {
                x
            }
        """.trimIndent())
            .shouldReport<ReadInPureContextDiagnostic>()
    }

    "mutating outside of a pure context" - {
        "by variable assignment" {
            validateModule("""
                var x = 1
                pure fn a() {
                    set x = 2
                }
            """.trimIndent())
                .shouldReport<AssignmentOutsideOfPurityBoundaryDiagnostic>()
        }

        "by calling a function that takes a mutable parameter" - {
            "global variable as parameter to simple function" {
                validateModule("""
                    class H {
                        var i = 0
                    }
                    x: mut _ = H()
                    fn pureMutate(p: mut H) {
                        set p.i = 1
                    }
                    read fn test() {
                        pureMutate(x)
                    }
                """.trimIndent())
                    .shouldReport<MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic>()
            }

            "global variable as self-parameter to member function" {
                validateModule("""
                    class H {
                        var i = 0
                        fn pureMutate(self: mut H) {
                            set self.i = 1
                        }
                    }
                    x: mut _ = H()
                    read fn test() {
                        x.pureMutate()
                    }
                """.trimIndent())
                    .shouldReport<MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic>()
            }

            "global variable as non-self parameter to member function" {
                validateModule("""
                    class H {
                        var i = 0
                    }
                    class K {
                        fn pureMutate(self, p: mut H) {
                            set p.i = 1
                        }
                    }
                    x: mut _ = H()
                    read fn test() {
                        k = K()
                        k.pureMutate(x)
                    }
                """.trimIndent())
                    .shouldReport<MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic>()
            }
        }
    }

    "mutation outside of a read context" {
        validateModule("""
            var x = 1
            read fn a() {
                set x = 2
            }
        """.trimIndent())
            .shouldReport<AssignmentOutsideOfPurityBoundaryDiagnostic>()
    }
})