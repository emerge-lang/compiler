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
            .shouldFind<ReadInPureContextDiagnostic>()
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
            .shouldFind<ImpureInvocationInPureContextDiagnostic>()
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
            .shouldFind<ModifyingInvocationInReadonlyContextDiagnostic>()
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
            .shouldFind<ModifyingInvocationInReadonlyContextDiagnostic>()
    }

    "reading from outside a pure context" {
        validateModule("""
            var x = 1
            pure fn a() {
                x
            }
        """.trimIndent())
            .shouldFind<ReadInPureContextDiagnostic>()
    }

    "mutating outside of a pure context" - {
        "by assignment" - {
            "global variable directly" {
                validateModule("""
                    var x = 1
                    pure fn a() {
                        set x = 2
                    }
                """.trimIndent())
                    .shouldFind<AssignmentOutsideOfPurityBoundaryDiagnostic>()
            }

            "property of a global variable" {
                validateModule("""
                    class Box {
                        var foo: const String = init
                    }
                    x: mut Box = Box("a")
                    fn test() {
                        set x.foo = "b"
                    }
                """.trimIndent())
                    .shouldFind<AssignmentOutsideOfPurityBoundaryDiagnostic>()
            }

            "nested property of a global variable" {
                validateModule("""
                    class Box {
                        var foo: const String = init
                    }
                    class G {
                        var box = Box("a")
                    }
                    x: mut G = G()
                    fn test() {
                        set x.box.foo = "b"
                    }
                """.trimIndent())
                    .shouldFind<AssignmentOutsideOfPurityBoundaryDiagnostic>()
            }
        }
    }

    "mutation outside of a read context" - {
        "by assignment" - {
            "global variable directly" {
                validateModule("""
                    var x = 1
                    read fn a() {
                        set x = 2
                    }
                """.trimIndent())
                    .shouldFind<AssignmentOutsideOfPurityBoundaryDiagnostic>()
            }

            "property of a global variable" {
                validateModule("""
                    class Box {
                        var foo: const String = init
                    }
                    x: mut Box = Box("a")
                    read fn test() {
                        set x.foo = "b"
                    }
                """.trimIndent())
                    .shouldFind<AssignmentOutsideOfPurityBoundaryDiagnostic>()
            }

            "nested property of a global variable" {
                validateModule("""
                    class Box {
                        var foo: const String = init
                    }
                    class G {
                        var box = Box("a")
                    }
                    x: mut G = G()
                    read fn test() {
                        set x.box.foo = "b"
                    }
                """.trimIndent())
                    .shouldFind<AssignmentOutsideOfPurityBoundaryDiagnostic>()
            }
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
                    .shouldFind<MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic>()
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
                    .shouldFind<MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic>()
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
                    .shouldFind<MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic>()
            }

            "passing a property of a global variable to a mutating function" {
                validateModule("""
                    class Box {
                        var foo: const String = init
                    }
                    class G {
                        var box = Box("a")
                    }
                    fn mutate(p: mut Box) {
                        set p.foo = "b"
                    }
                    x: mut G = G()
                    read fn test() {
                        mutate(x.box)
                    }
                """.trimIndent())
                    .shouldFind<MutableUsageOfStateOutsideOfPurityBoundaryDiagnostic>()
            }
        }
    }
})