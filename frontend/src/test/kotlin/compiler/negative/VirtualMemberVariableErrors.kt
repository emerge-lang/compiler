package compiler.compiler.negative

import compiler.ast.AstFunctionAttribute
import compiler.binding.AccessorKind
import compiler.diagnostic.AccessorContractViolationDiagnostic
import compiler.diagnostic.AmbiguousMemberVariableAccessDiagnostic
import compiler.diagnostic.ConflictingFunctionAttributesDiagnostic
import compiler.diagnostic.FunctionMissingAttributeDiagnostic
import compiler.diagnostic.GetterAndSetterHaveDifferentTypesDiagnostics
import compiler.diagnostic.MultipleAccessorsForVirtualMemberVariableDiagnostic
import compiler.diagnostic.NotAllMemberVariablesInitializedDiagnostic
import compiler.diagnostic.OverrideAccessorDeclarationMismatchDiagnostic
import compiler.diagnostic.VirtualAndActualMemberVariableNameClashDiagnostic
import compiler.lexer.Keyword
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.nulls.shouldNotBeNull
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.beInstanceOf

class VirtualMemberVariableErrors : FreeSpec({
    "marking a method both get and set produces a conflict" {
        validateModule("""
            class A {
                get set fn bla(self) -> S32 = 0
            }
        """.trimIndent())
            .shouldFind<ConflictingFunctionAttributesDiagnostic> {
                it.attributes should haveSize(2)
                it.attributes.forOne {
                    it.attributeName.keyword shouldBe Keyword.GET
                }
                it.attributes.forOne {
                    it.attributeName.keyword shouldBe Keyword.SET
                }
            }
    }

    "physical and virtual clash" - {
        "with getter only " {
            validateModule("""
                class A {
                    var n: S32 = 0
                    
                    get fn n(self) = 1
                }
            """.trimIndent())
                .shouldFind<VirtualAndActualMemberVariableNameClashDiagnostic> {
                    it.memberVar.name.value shouldBe "n"
                }
        }

        "with setter only " {
            validateModule("""
                class A {
                    var n: S32 = 0
                    
                    set fn n(self, value: S32) {}
                }
            """.trimIndent())
                .shouldFind<VirtualAndActualMemberVariableNameClashDiagnostic> {
                    it.memberVar.name.value shouldBe "n"
                }
        }

        "with getter and setter " {
            validateModule("""
                class A {
                    var n: S32 = 0
                    
                    get fn n(self) = 1
                    set fn n(self, value: S32) {}
                }
            """.trimIndent())
                .shouldFind<VirtualAndActualMemberVariableNameClashDiagnostic> {
                    it.memberVar.name.value shouldBe "n"
                }
        }
    }

    "mismatch with super fn" - {
        "super not declared accessor, override is" - {
            "override as get" {
                validateModule("""
                    interface I  {
                        fn bla(self) -> S32
                    }
                    class A : I {
                        override get fn bla(self) -> S32 = 0
                    }
                """.trimIndent())
                    .shouldFind<OverrideAccessorDeclarationMismatchDiagnostic>()
            }

            "override as set" {
                validateModule("""
                    interface I  {
                        fn bla(self, v: S32)
                    }
                    class A : I {
                        override set fn bla(self: mut _, v: S32) {}
                    }
                """.trimIndent())
                    .shouldFind<OverrideAccessorDeclarationMismatchDiagnostic>()
            }
        }

        "super declared accessor, override not" - {
            "super as get" {
                validateModule("""
                    interface I  {
                        get fn bla(self) -> S32
                    }
                    class A : I {
                        override fn bla(self) -> S32 = 0
                    }
                """.trimIndent())
                    .shouldFind<OverrideAccessorDeclarationMismatchDiagnostic>()
            }

            "override as set" {
                validateModule("""
                    interface I  {
                        get fn bla(self) -> S32
                    }
                    class A : I {
                        override fn bla(self) -> S32 {}
                    }
                """.trimIndent())
                    .shouldFind<OverrideAccessorDeclarationMismatchDiagnostic>()
            }
        }
    }

    "contract verification" - {
        "getters" - {
            "must take a single self argument" - {
                "no arguments" {
                    validateModule("""
                        interface I {
                            get fn bla() -> S32
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }
                "two arguments" {
                    validateModule("""
                        interface I {
                            get fn bla(self, foo: S32) -> S32
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }
            }

            "self argument must be readonly" - {
                "explicitly declared mut" {
                    validateModule("""
                        interface I {
                            get fn bla(self: mut _) -> S32
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "explicitly declared const" {
                    validateModule("""
                        interface I {
                            get fn bla(self: const _) -> S32
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "explicitly declared exclusive" {
                    validateModule("""
                        interface I {
                            get fn bla(self: exclusive _) -> S32
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "mutable through generic bound" {
                    validateModule("""
                        interface I {
                            get fn bla<S : mut Any>(self: S) -> S32
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }
            }

            "self argument must be borrowed" {
                validateModule("""
                    interface I {
                        get fn bla(capture self) -> S32
                    }
                """.trimIndent())
                    .shouldFind<AccessorContractViolationDiagnostic> {
                        it.accessor.name.value shouldBe "bla"
                    }
            }

            "must be pure" - {
                "explicitly declared read" {
                    validateModule("""
                        interface I {
                            read get fn bla(self) -> S32
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "explicitly declared mut" {
                    validateModule("""
                        interface I {
                            mut get fn bla(self) -> S32
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }
            }
        }
        "setters" - {
            "must take two arguments, the first being a receiver" - {
                "no arguments" {
                    validateModule("""
                        interface I {
                            set fn bla()
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "one argument, receiver" {
                    validateModule("""
                        interface I {
                            set fn bla(self: mut _)
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "one argument, not receiver" {
                    validateModule("""
                        class A {}
                        interface I {
                            set fn bla(other: mut A)
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "two arguments, no receiver" {
                    validateModule("""
                        class A {}
                        interface I {
                            set fn bla(other: mut A, value: S32)
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "three arguments with receiver" {
                    validateModule("""
                        interface I {
                            set fn bla(self: mut _, value1: S32, value2: S32)
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }
            }

            "self argument must be borrowed" {
                validateModule("""
                    interface I {
                        set fn bla(capture self: mut _, v: S32)
                    }
                """.trimIndent())
                    .shouldFind<AccessorContractViolationDiagnostic> {
                        it.accessor.name.value shouldBe "bla"
                    }
            }

            "self argument must be mutable" - {
                "explicitly declared const" {
                    validateModule("""
                        interface I {
                            set fn bla(self: const _, v: S32)
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "explicitly declared read" {
                    validateModule("""
                        interface I {
                            set fn bla(self: read _, v: S32)
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "explicitly declared exclusive" {
                    validateModule("""
                        interface I {
                            set fn bla(self: exclusive _, v: S32)
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }
            }

            "must be pure" - {
                "explicitly declared read" {
                    validateModule("""
                        interface I {
                            read set fn bla(self: mut _, v: S32)
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }

                "explicitly declared mut" {
                    validateModule("""
                        interface I {
                            mut set fn bla(self: mut _, v: S32)
                        }
                    """.trimIndent())
                        .shouldFind<AccessorContractViolationDiagnostic> {
                            it.accessor.name.value shouldBe "bla"
                        }
                }
            }

            "must return Unit" {
                validateModule("""
                    interface I {
                        set fn bla(self: mut _, v: S32) -> Bool
                    }
                """.trimIndent())
                    .shouldFind<AccessorContractViolationDiagnostic> {
                        it.accessor.name.value shouldBe "bla"
                    }
            }
        }
    }

    "across multiple accessors" - {
        // getters can't collide as members of a base type because they'll form an overload-set and then clash
        // with each other, resulting in a diagnostic pointing that out. So no need to produce a second diagnostic
        // that is just noisy
        // getters on package level cannot collide, because they'll also form an overload set. If the overloads
        // are ambiguous, that results in a diagnostic. Same thing as on basetype level. If they are unambiguous,
        // that is fine. It must be okay, so one can define a getter on two distinct types that happen to have the same name

        // collisions across multiple packages are handled by the ambiguity-handling of invocationexpression

        "two setters in the same base type" {
            validateModule("""
                interface I {
                    set fn bla(self: mut _, value: S32)
                    set fn bla(self: mut _, value: UWord)
                }
            """.trimIndent())
                .shouldFind<MultipleAccessorsForVirtualMemberVariableDiagnostic> {
                    it.memberVarName shouldBe "bla"
                    it.kind shouldBe AccessorKind.Write
                }
        }

        "two setters in the same package" {
            validateModule("""
                interface I {}
                
                set fn bla(self: mut I, value: S32) {}
                set fn bla(self: mut I, value: UWord) {}
            """.trimIndent())
                .shouldFind<MultipleAccessorsForVirtualMemberVariableDiagnostic> {
                    it.memberVarName shouldBe "bla"
                    it.kind shouldBe AccessorKind.Write
                }
        }

        "getter and setter have different type" - {
            "on base type level" {
                validateModule("""
                    interface I {
                        get fn bla(self) -> S32
                        set fn bla(self: mut _, value: UWord)
                    }
                """.trimIndent())
                    .shouldFind<GetterAndSetterHaveDifferentTypesDiagnostics> {
                        it.getter.name.value shouldBe "bla"
                        it.setter.name.value shouldBe "bla"
                    }
            }

            "on package level" {
                validateModule("""
                    interface I {}
                    interface Decoy {}
                    
                    get fn bla(self: I) -> S32 = 0
                    set fn bla(self: mut I, value: UWord) {}
                    set fn bla(self: mut Decoy, value: SWord) {} // this should be ignored because Decoy and I are disjoint
                """.trimIndent())
                    .shouldFind<GetterAndSetterHaveDifferentTypesDiagnostics> {
                        it.getter.name.value shouldBe "bla"
                        it.setter.name.value shouldBe "bla"
                        it.setter.parameters.parameters.firstOrNull().shouldNotBeNull().type.shouldNotBeNull().simpleName shouldBe "I"
                    }
            }
        }
    }

    "use-site ambiguity" - {
        "between multiple package-level getters" {
            validateModule("""
                // defining X and Y as disjoint types helps declare two identically-named getters in the same packag
                interface X {}
                interface Y {}
                class C : X, Y {}
                get fn p(self: X) -> Bool = false
                get fn p(self: Y) -> Bool = true
                fn test() {
                    l = C().p
                }
            """.trimIndent())
                .shouldFind< AmbiguousMemberVariableAccessDiagnostic> {
                    it.memberVariableName shouldBe "p"
                }
        }

        "between multiple package-level setters" {
            validateModule("""
                interface X {}
                interface Y {}
                class C : X, Y {}
                set fn m(self: mut X, value: S32) {}
                set fn m(self: mut Y, value: String) {}
                fn test() {
                    var l = C()
                    set l.m = 3
                }
            """.trimIndent())
                .shouldFind<AmbiguousMemberVariableAccessDiagnostic>() {
                    it.memberVariableName shouldBe "m"
                }
        }

        "between package-level getter and actual member variable" {
            validateModule("""
                class C {
                    p: Bool = false
                }
                get fn p(self: C) -> Bool = true
                fn test() {
                    l = C().p
                }
            """.trimIndent())
                .shouldFind< AmbiguousMemberVariableAccessDiagnostic> {
                    it.memberVariableName shouldBe "p"
                }
        }

        "between package-level setter and actual member variable" {
            validateModule("""
                class C {
                    var p: S32 = 0
                }
                set fn p(self: mut C, value: String) {}
                fn test() {
                    var l = C()
                    set l.p = 3
                }
            """.trimIndent())
                .shouldFind<AmbiguousMemberVariableAccessDiagnostic>() {
                    it.memberVariableName shouldBe "p"
                }
        }

        "between package-level getter and member-fn-getter" {
            validateModule("""
                class C {
                    get fn p(self: C) -> Bool = false
                }
                get fn p(self: C) -> Bool = true
                fn test() {
                    l = C().p
                }
            """.trimIndent())
                .shouldFind<AmbiguousMemberVariableAccessDiagnostic> {
                    it.memberVariableName shouldBe "p"
                }
        }

        "between package-level setter and member-fn-setter" {
            validateModule("""
                class C {
                    set fn p(self: C, v: Bool) {}
                }
                set fn p(self: C, v: S32) {}
                fn test() {
                    var l = C()
                    set l.p = 3
                }
            """.trimIndent())
                .shouldFind<AmbiguousMemberVariableAccessDiagnostic> {
                    it.memberVariableName shouldBe "p"
                }
        }
    }

    "missing function attribute" - {
        "on package level getter" {
            validateModule("""
                interface I {}
                fn foo(self: I) -> S32 = 0
                fn test(p: I) = p.foo
            """.trimIndent())
                .shouldFind<FunctionMissingAttributeDiagnostic> {
                    it.function.name shouldBe "foo"
                    it.attribute should beInstanceOf<AstFunctionAttribute.Accessor>()
                    (it.attribute as AstFunctionAttribute.Accessor).kind shouldBe AccessorKind.Read
                }
        }

        "on member getter" {
            validateModule("""
                interface I {
                    fn foo(self) -> S32
                }
                fn test(p: I) = p.foo
            """.trimIndent())
                .shouldFind<FunctionMissingAttributeDiagnostic> {
                    it.function.name shouldBe "foo"
                    it.attribute should beInstanceOf<AstFunctionAttribute.Accessor>()
                    (it.attribute as AstFunctionAttribute.Accessor).kind shouldBe AccessorKind.Read
                }
        }

        "on package level setter" {
            validateModule("""
                interface I {}
                fn foo(self: I, v: S32) {}
                fn test(p: mut I) {
                    set p.foo = 3
                }
            """.trimIndent())
                .shouldFind<FunctionMissingAttributeDiagnostic> {
                    it.function.name shouldBe "foo"
                    it.attribute should beInstanceOf<AstFunctionAttribute.Accessor>()
                    (it.attribute as AstFunctionAttribute.Accessor).kind shouldBe AccessorKind.Write
                }
        }

        "on member setter" {
            validateModule("""
                interface I {
                    fn foo(self, v: S32)
                }
                fn test(p: mut I) {
                    set p.foo = 3
                }
            """.trimIndent())
                .shouldFind<FunctionMissingAttributeDiagnostic> {
                    it.function.name shouldBe "foo"
                    it.attribute should beInstanceOf<AstFunctionAttribute.Accessor>()
                    (it.attribute as AstFunctionAttribute.Accessor).kind shouldBe AccessorKind.Write
                }
        }
    }

    "accessors require a fully initialized object" - {
        "member getter" {
            validateModule("""
                class Test {
                    n: S32
                
                    get fn foo(self) -> Bool = false
                
                    constructor {
                        localBool = self.foo
                        set self.n = 3
                    }
                }
            """.trimIndent())
                .shouldFind<NotAllMemberVariablesInitializedDiagnostic>()
        }

        "member setter" {
            validateModule("""
                class Test {
                    n: S32
                
                    set fn foo(self: mut _, v: Bool) {}
                
                    constructor {
                        set self.foo = false
                        set self.n = 3
                    }
                }
            """.trimIndent())
                .shouldFind<NotAllMemberVariablesInitializedDiagnostic>()
        }
    }
})