package compiler.compiler.negative

import compiler.binding.impurity.ImpureInvocation
import compiler.binding.impurity.ReadingVariableBeyondBoundary
import compiler.binding.impurity.ReassignmentBeyondBoundary
import compiler.binding.impurity.VariableUsedAsMutable
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

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
            .shouldFind<PurityViolationDiagnostic> {
                it.impurity.shouldBeInstanceOf<ReadingVariableBeyondBoundary>()
            }
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
            .shouldFind<PurityViolationDiagnostic> {
                it.impurity.shouldBeInstanceOf<ImpureInvocation>()
            }
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
            .shouldFind<PurityViolationDiagnostic> {
                it.impurity.shouldBeInstanceOf<ImpureInvocation>()
            }
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
            .shouldFind<PurityViolationDiagnostic> {
                it.impurity.shouldBeInstanceOf<ImpureInvocation>()
            }
    }

    "reading from outside a pure context" {
        validateModule("""
            var x = 1
            fn a() {
                x
            }
        """.trimIndent())
            .shouldFind<PurityViolationDiagnostic> {
                it.impurity.shouldBeInstanceOf<ReadingVariableBeyondBoundary>()
            }
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<ReassignmentBeyondBoundary>()
                    }
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<ReassignmentBeyondBoundary>()
                    }
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<ReassignmentBeyondBoundary>()
                    }
            }
        }

        // return as mut type not relevant, because even reading the global is not allowed in pure context
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<ReassignmentBeyondBoundary>()
                    }
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<ReassignmentBeyondBoundary>()
                    }
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<ReassignmentBeyondBoundary>()
                    }
            }

            "assigning a global variable to a local variable of mutable type" - {
                "in initializer" {
                    validateModule("""
                        class Box {
                            var n: S32 = 0
                        }
                        var globalBox = Box()
                        read fn test() {
                            localBox: mut Box = globalBox
                        }
                    """.trimIndent())
                        .shouldFind<PurityViolationDiagnostic> {
                            it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                        }
                }

                "in assigment statement" - {
                    "directly" {
                        validateModule("""
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox = Box()
                            read fn test() {
                                localBox: mut Box
                                set localBox = globalBox
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }
                    }

                    "through if-else" {
                        validateModule("""
                            intrinsic read fn random() -> Bool
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox = Box()
                            read fn test() {
                                localBox: mut Box
                                set localBox = if (random()) globalBox else Box()
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }

                        validateModule("""
                            intrinsic read fn random() -> Bool
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox = Box()
                            read fn test() {
                                localBox: mut Box
                                set localBox = if (random()) Box() else globalBox
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }
                    }

                    "through try-catch" {
                        validateModule("""
                            intrinsic read fn randomThrow()
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox = Box()
                            read fn test() {
                                localBox: mut Box
                                set localBox = try {
                                    randomThrow()
                                    globalBox
                                } catch e {
                                    Box()
                                }
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }

                        validateModule("""
                            intrinsic read fn randomThrow()
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox = Box()
                            read fn test() {
                                localBox: mut Box
                                set localBox = try {
                                    randomThrow()
                                    Box()
                                } catch e {
                                    globalBox
                                }
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }
                    }

                    "through array literal" {
                        validateModule("""
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox = Box()
                            read fn test() {
                                localBox: Array<mut Box>
                                set localBox = [globalBox]
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }

                        validateModule("""
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox = Box()
                            read fn test() {
                                localBox: Array<read Box>
                                set localBox = [globalBox]
                            }
                        """.trimIndent())
                            .shouldHaveNoDiagnostics()
                    }

                    "through not null expression" {
                        validateModule("""
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox: mut Box? = Box()
                            read fn test() {
                                localBox: mut Box = globalBox!!
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }
                    }

                    "through null-coalescing expression" {
                        validateModule("""
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox: mut Box? = Box()
                            read fn test() {
                                localBox: mut Box
                                set localBox = globalBox ?: Box()
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }

                        validateModule("""
                            class Box {
                                var n: S32 = 0
                            }
                            var globalBox: mut Box? = Box()
                            read fn test() {
                                localBox: mut Box
                                set localBox = Box() ?: globalBox
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }
                    }

                    "through throw expression" {
                        validateModule("""
                            class SampleEx : Throwable {
                                constructor {
                                    mixin ThrowableTrait("foo")
                                }
                            }
                            var globalEx: mut SampleEx = SampleEx()
                            read fn test() {
                                throw globalEx
                            }
                        """.trimIndent())
                            .shouldFind<PurityViolationDiagnostic> {
                                it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                            }
                    }

                    "through member accesses" - {
                        "nesting depth 1" {
                            validateModule("""
                                class Box1 {
                                    var n: S32 = 1
                                }
                                class Box2 {
                                    var b1: mut Box1 = Box1()
                                }
                                var globalBox2: mut Box2 = Box2()
                                read fn test() {
                                    localBox1: mut Box1
                                    set localBox1 = globalBox2.b1
                                }
                            """.trimIndent()
                            )
                                .shouldFind<PurityViolationDiagnostic> {
                                    it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                                }
                        }

                        "nesting depth 2" {
                            validateModule("""
                                class Box1 {
                                    var n: S32 = 1
                                }
                                class Box2 {
                                    var b1: mut Box1 = Box1()
                                }
                                class Box3 {
                                    var b2: mut Box2 = Box2()
                                }
                                var globalBox3: mut Box3 = Box3()
                                read fn test() {
                                    localBox1: mut Box1
                                    set localBox1 = globalBox3.b2.b1
                                }
                            """.trimIndent())
                                .shouldFind<PurityViolationDiagnostic> {
                                    it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                                }
                        }

                        "nesting depth 3" {
                            validateModule("""
                                class Box1 {
                                    var n: S32 = 1
                                }
                                class Box2 {
                                    var b1: mut Box1 = Box1()
                                }
                                class Box3 {
                                    var b2: mut Box2 = Box2()
                                }
                                class Box4 {
                                    var b3: mut Box3 = Box3()
                                }
                                var globalBox4: mut Box4 = Box4()
                                read fn test() {
                                    localBox1: mut Box1
                                    set localBox1 = globalBox4.b3.b2.b1
                                }
                            """.trimIndent())
                                .shouldFind<PurityViolationDiagnostic> {
                                    it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                                }
                        }
                    }
                }
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                    }
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                    }
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                    }
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                    }
            }
        }

        "by returning as a mut type" - {
            "through return statement" {
                validateModule("""
                    class Box {
                        var n: S32 = 0
                    }
                    var globalBox = Box()
                    read fn test() -> mut Box {
                        return globalBox
                    }
                """.trimIndent())
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                    }
            }

            "through single expression fn body" {
                validateModule("""
                    class Box {
                        var n: S32 = 0
                    }
                    var globalBox = Box()
                    read fn test() -> mut Box = globalBox
                """.trimIndent())
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<VariableUsedAsMutable>()
                    }
            }
        }
    }

    "object traversal limits mutability" - {
        // exclusive mutability on object members is currently not allowed, so no need to test

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