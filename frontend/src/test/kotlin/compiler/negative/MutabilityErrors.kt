package compiler.compiler.negative

import compiler.diagnostic.SimultaneousIncompatibleBorrowsDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class MutabilityErrors : FreeSpec({
    "class initialized in a val is immutable" - {
        "members cannot be mutated" {
            validateModule("""
                class X {
                    var a: S32 = init
                }
                fn test() {
                    myX = X(2)
                    set myX.a = 3
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "cannot be assigned to a mut reference" {
            validateModule("""
                class X {
                    a: S32 = init
                }
                fn test() {
                    myX = X(2)
                    var otherX: mut X = myX
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.reason shouldBe "cannot assign a const value to a mut reference"
                }
        }

        "can be assigned to an const reference" {
            validateModule("""
                class X {
                    a: S32 = init
                }
                fn test() {
                    myX = X(2)
                    otherX: const X = myX
                }
            """.trimIndent()) should haveNoDiagnostics()
        }
    }

    "mutability from use-site generics" - {
        "prohibits writes to const element" {
            validateModule("""
                class A {
                    someVal: S32 = init
                }
                class B<T> {
                    var genericVal: T = init
                }
                fn test() {
                    myB: mut B<const A> = B::<const A>(A(3))
                    set myB.genericVal = A(2)
                    set myB.genericVal.someVal = 5
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.targetType.toString() shouldBe "mut testmodule.A"
                    it.sourceType.toString() shouldBe "const testmodule.A"
                }
        }
    }

    "mutability errors when calling functions" - {
        "mut value to const parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fn foo(p: const S) {}
                fn test(p: mut S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "A const value is needed here, this one is mut."
                }
        }

        "read value to mut parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fn foo(p: mut S) {}
                fn test(p: read S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "Cannot mutate this value, this is a read reference."
                }
        }

        "read value to const parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fn foo(p: const S) {}
                fn test(p: read S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "A const value is needed here. This is a read reference, immutability is not guaranteed."
                }
        }

        "const value to mut parameter" {
            validateModule("""
                class S {
                    field: S32
                }
                fn foo(p: mut S) {}
                fn test(p: const S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "Cannot mutate this value. In fact, this is an const value."
                }
        }

        "mut value to exclusive parameter" {
            validateModule("""
                class S {
                    field: S32 = init
                }
                fn foo(p: exclusive S) {}
                fn test(p: mut S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "An exclusive value is needed here, this one is mut."
                }
        }

        "read value to exclusive parameter" {
            validateModule("""
                class S {
                    field: S32 = init
                }
                fn foo(p: exclusive S) {}
                fn test(p: read S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "An exclusive value is needed here; this is a read reference."
                }
        }

        "const value to exclusive parameter" {
            validateModule("""
                class S {
                    field: S32 = init
                }
                fn foo(p: exclusive S) {}
                fn test(p: const S) {
                    foo(p)
                }
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.message shouldBe "An exclusive value is needed here, this one is const."
                }
        }
    }

    "member variable access" - {
        "read" - {
            "ref variable remains mut through read and const parent objs" {
                // TODO: make const more strict, reintroduce readconst mutability??
                validateModule("""
                    class Box {
                        var x: S32 = 0
                    }
                    class Foo {
                        ref box: mut Box = Box()
                    }
                    
                    fn test1(p: read Foo) {
                        l: mut Box = p.box
                    }
                    
                    fn test2(p: const Foo) {
                        l: mut Box = p.box
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "owned member variable is mut or const, depending on parent object" {
                validateModule("""
                    class Box {
                        var x: S32 = 0
                    }
                    class Foo {
                        own box = Box()
                    }
                    
                    fn test(p: const Foo) {
                        l: mut Box = p.box
                    }
                """.trimIndent())
                    .shouldFind< ValueNotAssignableDiagnostic>() {
                        it.sourceType.toString() shouldBe "const testmodule.Box"
                        it.targetType.toString() shouldBe "mut testmodule.Box"
                    }

                validateModule("""
                    class Box {
                        var x: S32 = 0
                    }
                    class Foo {
                        own box = Box()
                    }
                    
                    fn test(p: mut Foo) {
                        l: const Box = p.box
                    }
                """.trimIndent())
                    .shouldFind< ValueNotAssignableDiagnostic>() {
                        it.sourceType.toString() shouldBe "mut testmodule.Box"
                        it.targetType.toString() shouldBe "const testmodule.Box"
                    }
            }

            "decoration semantics for owned and ctor-initialized member variables" - {
                "mutability determined on the constructors call site when ctor param is exclusive" {
                    validateModule("""
                        class Box {
                            var x: S32 = 0
                        }
                        class Foo {
                            own box : Box = init
                        }
                        
                        fn test() {
                            l1: mut Foo = Foo(Box())
                            l2: const Foo = Foo(Box())
                        }
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }

                "mutability determined by the parameter when ctor param is not exclusive" {
                    validateModule("""
                        class Box {
                            var x: S32 = 0
                        }
                        class Foo {
                            own box : Box = init
                        }
                        
                        fn test(p: read Box) {
                            l1 = Foo(p)
                            l2: mut Box = l1
                        }
                    """.trimIndent())
                        .shouldFind< ValueNotAssignableDiagnostic>() {
                            it.sourceType.toString() shouldBe "read testmodule.Box"
                            it.targetType.toString() shouldBe "mut testmodule.Box"
                        }

                    validateModule("""
                        class Box {
                            var x: S32 = 0
                        }
                        class Foo {
                            own box : Box = init
                        }
                        
                        fn test(p: mut Box) {
                            var l1 = Foo(p)
                            l2: const Box = l1
                        }
                    """.trimIndent())
                        .shouldFind< ValueNotAssignableDiagnostic>() {
                            it.sourceType.toString() shouldBe "mut testmodule.Box"
                            it.targetType.toString() shouldBe "const testmodule.Box"
                        }

                    validateModule("""
                        class Box {
                            var x: S32 = 0
                        }
                        class Foo {
                            own box: Box = init
                        }
                        
                        fn test(p: const Box) {
                            var  l1 = Foo(p)
                            l2: mut Box = l1
                        }
                    """.trimIndent())
                        .shouldFind< ValueNotAssignableDiagnostic>() {
                            it.sourceType.toString() shouldBe "const testmodule.Box"
                            it.targetType.toString() shouldBe "mut testmodule.Box"
                        }
                }
            }

            "decoration semantics on exclusive objects" - {
                val box = """
                    class Box {
                        var x: S32 = 0
                    }
                """.trimIndent()
                val foo = """
                    class Foo {
                        own box: Box = Box()
                    }
                """.trimIndent()
                "cannot alias member variable on exclusive object as mut" {
                    validateModule("""
                        $box
                        $foo
                        
                        fn test() {
                            exclFoo: exclusive _ = Foo()
                            l: mut Box = exclFoo.box
                        }
                    """.trimIndent())
                        .shouldFind<ValueNotAssignableDiagnostic> {
                            it.sourceType.toString() shouldBe "read testmodule.Foo"
                            it.targetType.toString() shouldBe "mut testmodule.Foo"
                        }
                }

                "cannot alias member variable on exclusive object as const" {
                    validateModule("""
                        $box
                        $foo
                        
                        fn test() {
                            exclFoo: exclusive _ = Foo()
                            l: const Box = exclFoo.box
                        }
                    """.trimIndent())
                        .shouldFind<ValueNotAssignableDiagnostic> {
                            it.sourceType.toString() shouldBe "read testmodule.Foo"
                            it.targetType.toString() shouldBe "const testmodule.Foo"
                        }
                }

                "CAN alias member variable on exclusive object as read" {
                    validateModule("""
                        $box
                        $foo
                        
                        fn test() {
                            exclFoo: exclusive _ = Foo()
                            l: read Box = exclFoo.box
                        }
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }

                "CAN borrow member variable from exclusive object as exclusive" {
                    validateModule("""
                        $box
                        $foo
                        
                        fn test() {
                            exclFoo: exclusive _ = Foo()
                            
                            borrowExclusive(exclFoo.box)
                            borrowMut(exclFoo.box)
                            borrowConst(exclFoo.box)
                        }
                        
                        intrinsic fn borrowExclusive(p: exclusive Box)
                        intrinsic fn borrowMut(p: mut Box)
                        intrinsic fn borrowConst(p: const Box)
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }

                "CANNOT borrow member variables from exclusive object as mut and const at the same time" {
                    validateModule("""
                        $box
                        
                        class Foo {
                            own b1 = Box()
                            own b2 = Box()
                        }
                        
                        fn test() {
                            exclFoo: exclusive _ = Foo()
                            borrowMutAndConst(exclFoo.b1, exclFoo.b2)
                        }
                        
                        intrinsic fn borrowMutAndConst(p1: mut Box, p2: const Box)
                    """.trimIndent())
                        .shouldFind<SimultaneousIncompatibleBorrowsDiagnostic>()
                }
            }
        }
    }
})