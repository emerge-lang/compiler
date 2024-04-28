package compiler.compiler.negative

import compiler.reportings.AbstractInheritedFunctionNotImplementedReporting
import compiler.reportings.AmbiguousFunctionOverrideReporting
import compiler.reportings.ClassMemberVariableNotInitializedDuringObjectConstructionReporting
import compiler.reportings.ConstructorDeclaredModifyingReporting
import compiler.reportings.DuplicateBaseTypeMemberReporting
import compiler.reportings.DuplicateSupertypeReporting
import compiler.reportings.ExplicitOwnershipNotAllowedReporting
import compiler.reportings.ExternalMemberFunctionReporting
import compiler.reportings.IllegalFunctionBodyReporting
import compiler.reportings.IllegalSupertypeReporting
import compiler.reportings.ImpureInvocationInPureContextReporting
import compiler.reportings.IncompatibleReturnTypeOnOverrideReporting
import compiler.reportings.MissingFunctionBodyReporting
import compiler.reportings.MultipleClassConstructorsReporting
import compiler.reportings.MultipleClassDestructorsReporting
import compiler.reportings.ObjectNotFullyInitializedReporting
import compiler.reportings.OverloadSetHasNoDisjointParameterReporting
import compiler.reportings.ReadInPureContextReporting
import compiler.reportings.Reporting
import compiler.reportings.StateModificationOutsideOfPurityBoundaryReporting
import compiler.reportings.StaticFunctionDeclaredOverrideReporting
import compiler.reportings.SuperFunctionForOverrideNotFoundReporting
import compiler.reportings.TypeArgumentOutOfBoundsReporting
import compiler.reportings.TypeParameterNameConflictReporting
import compiler.reportings.UndeclaredOverrideReporting
import compiler.reportings.UnknownTypeReporting
import compiler.reportings.UseOfUninitializedClassMemberVariableReporting
import compiler.reportings.ValueNotAssignableReporting
import io.kotest.assertions.fail
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forAll
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class ClassErrors : FreeSpec({
    "duplicate member" {
        validateModule("""
            class X {
                a: Int
                b: Int
                a: Boolean
            }
        """.trimIndent())
            .shouldReport<DuplicateBaseTypeMemberReporting> {
                it.duplicates should haveSize(2)
                it.duplicates.forAll {
                    it.name shouldBe "a"
                }
            }
    }

    "unknown declared member type" {
        validateModule("""
            class X {
                a: Foo
            }
        """.trimIndent())
            .shouldReport<UnknownTypeReporting>()
    }

    "calling a constructor with incorrect argument types" {
        validateModule("""
            class X {
                a: Int = init
            }
            
            fun foo() {
                x = X(true)
            }
        """.trimIndent())
            .shouldReport<ValueNotAssignableReporting>()
    }

    "calling a hypothetical constructor of a non-existent type" {
        validateModule("""
            x = Nonexistent()
        """.trimIndent())
    }

    "member variables" - {
        "class member variables must be initialized" {
            validateModule("""
                class Foo {
                    x: Int
                }
            """.trimIndent())
                .shouldReport<ClassMemberVariableNotInitializedDuringObjectConstructionReporting>()
        }

        "members can be initialized in the custom constructor by assignment" {
            validateModule("""
                class Foo {
                    x: Int
                    
                    constructor {
                        set self.x = 3
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "class member variable initializers are pure" - {
            "cannot read" {
                validateModule("""
                    var x: Int = 3
                    class Foo {
                        y: Int = x
                    }
                """.trimIndent())
                    .shouldReport<ReadInPureContextReporting>()
            }

            "cannot call readonly functions" {
                validateModule("""
                    intrinsic readonly fun bar() -> Int
                    class Foo {
                        x: Int = bar()
                    }
                """.trimIndent())
                    .shouldReport<ImpureInvocationInPureContextReporting>()
            }

            // TODO: as soon as there are lambdas, add a test to verify a run { ... } initializer can't write
        }

        "cannot declare ownership" {
            validateModule("""
                class Foo {
                    borrow x: Int
                }
            """.trimIndent())
                .shouldReport<ExplicitOwnershipNotAllowedReporting>()
        }
    }

    "member functions" - {
        "must have a body" {
            validateModule("""
                class Test {
                    fun test(self)
                }
            """.trimIndent())
                .shouldReport<MissingFunctionBodyReporting>()
        }

        "intrinsic must not have a body" {
            validateModule("""
                class Test {
                    intrinsic fun test(self) {}
                }
            """.trimIndent())
                .shouldReport<IllegalFunctionBodyReporting>()
        }

        "cannot be external" - {
            "on class" {
                validateModule("""
                    class Test {
                        external(C) fun foo()
                    }
                """.trimIndent())
                    .shouldReport<ExternalMemberFunctionReporting>()
            }

            "on interface" {
                validateModule("""
                    interface Test {
                        external(C) fun foo()
                    }
                """.trimIndent())
                    .shouldReport<ExternalMemberFunctionReporting>()
            }
        }

        "must implement all abstract supertype functions" - {
            "single degree of inheritance" {
                validateModule("""
                    interface Animal {
                        fun makeSound(self)
                    }
                    class Dog : Animal {}
                """.trimIndent())
                    .shouldReport<AbstractInheritedFunctionNotImplementedReporting>()
            }

            "two degrees of inheritance" {
                validateModule("""
                    interface Animal {
                        fun makeSound(self)
                    }
                    interface QuadraPede : Animal {}
                    class Dog : QuadraPede {}
                """.trimIndent())
                    .shouldReport<AbstractInheritedFunctionNotImplementedReporting>()
            }

            "first degree of inheritance implements abstract method from second degree" {
                validateModule("""
                    interface Animal {
                        fun makeSound(self)
                    }
                    interface QuadraPede : Animal {
                        override fun makeSound(self) {}
                    }
                    class Dog : QuadraPede {}
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }
        }
    }

    "constructor" - {
        "can only declare one" {
            validateModule("""
                class Foo {
                    constructor {
                    }
                    constructor {
                    }
                }
            """.trimIndent())
                .shouldReport<MultipleClassConstructorsReporting>()
        }

        "member variable uninitialized" - {
            "constructor cannot use that member variables" {
                validateModule("""
                    class Foo {
                        x: Int
                        y: Int = 2
                        
                        constructor {
                            doSomething(self.y)
                            doSomething(self.x)
                            set self.x = 3
                            doSomething(self.x)
                        }
                    }
                    
                    fun doSomething(p: Int) {}
                """.trimIndent())
                    .shouldReport<UseOfUninitializedClassMemberVariableReporting> {
                        it.member.name.value shouldBe "x"
                    }
            }

            "constructor cannot use self" {
                validateModule("""
                    class Foo {
                        x: Int
                        y: Int = 2
                        
                        constructor {
                            doSomething(self)
                            set self.x = 3
                            doSomething(self)
                        }
                    }
                    
                    fun doSomething(p: Foo) {}
                """.trimIndent())
                    .shouldReport<ObjectNotFullyInitializedReporting> {
                        it.uninitializedMembers should haveSize(1)
                        it.uninitializedMembers.single().name.value shouldBe "x"
                    }
            }
        }

        "member variable has maybe been initialized" - {
            "constructor cannot use that member variable" {
                validateModule("""
                    class Foo {
                        cond: Boolean = init
                        x: Int
                        
                        constructor {
                            if self.cond {
                                set self.x = 3
                            }
                            doSomething(self.x)
                        }
                    }
                    
                    fun doSomething(p: Int) {}
                """.trimIndent())
                    .shouldReport<UseOfUninitializedClassMemberVariableReporting> {
                        it.member.name.value shouldBe "x"
                    }
            }

            "constructor cannot use self" {
                validateModule("""
                    class Foo {
                        cond: Boolean = init
                        x: Int
                        
                        constructor {
                            if self.cond {
                                set self.x = 3
                            }
                            doSomething(self)
                        }
                    }
                    
                    fun doSomething(p: Foo) {}
                """.trimIndent())
                    .shouldReport<ObjectNotFullyInitializedReporting> {
                        it.uninitializedMembers should haveSize(1)
                        it.uninitializedMembers.single().name.value shouldBe "x"
                    }
            }
        }

        "member variable has been initialized in two different ways" - {
            "constructor can use that member variable" {
                validateModule("""
                    class Foo {
                        cond: Boolean = init
                        x: Int
                        
                        constructor {
                            if self.cond {
                                set self.x = 3
                            } else {
                                set self.x = 4
                            }
                            doSomething(self.x)
                        }
                    }
                    
                    fun doSomething(p: Int) {}
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "constructor can use self" {
                validateModule("""
                    class Foo {
                        cond: Boolean = init
                        x: Int
                        
                        constructor {
                            if self.cond {
                                set self.x = 3
                            } else {
                                set self.x = 4
                            }
                            doSomething(self)
                        }
                    }
                    
                    fun doSomething(borrow p: Foo) {}
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }
        }

        "purity" - {
            "constructor is pure by default" - {
                "cannot read global state" {
                    validateModule("""
                        intrinsic readonly fun foo() -> Int
                        x: Int = foo()
                        class Test {
                            y: Int
                            constructor {
                                set self.y = x
                            }
                        }
                    """.trimIndent())
                        .shouldReport<ReadInPureContextReporting>()
                }

                "cannot write global state" {
                    validateModule("""
                        var x: Int = 0
                        class Test {
                            constructor {
                                set x = 1
                            }
                        }
                    """.trimIndent())
                        .shouldReport<StateModificationOutsideOfPurityBoundaryReporting>()
                }
            }

            "constructor declared as readonly" - {
                "can read global state" {
                    validateModule("""
                        intrinsic readonly fun foo() -> Int
                        x: Int = foo()
                        class Test {
                            y: Int
                            readonly constructor {
                                set self.y = x
                            }
                        }
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }

                "cannot write global state" {
                    validateModule("""
                        var x: Int = 0
                        class Test {
                            readonly constructor {
                                set x = 1
                            }
                        }
                    """.trimIndent())
                        .shouldReport<StateModificationOutsideOfPurityBoundaryReporting>()
                }
            }

            "constructor cannot be declared modifying" {
                validateModule("""
                    var x = 0
                    class Test {
                        mutable constructor {
                            set x = 1
                        }
                    }
                """.trimIndent())
                    .shouldReport<ConstructorDeclaredModifyingReporting>()
            }
        }
    }

    "destructor" - {
        "can only declare one" {
            validateModule("""
                class Foo {
                    destructor {
                    }
                    destructor {
                    }
                }
            """.trimIndent())
                .shouldReport<MultipleClassDestructorsReporting>()
        }
    }

    "generics" - {
        "type parameter with unresolvable bound" {
            validateModule("""
                class X<T : Bla> {}
            """.trimIndent())
                .shouldReport<UnknownTypeReporting> {
                    it.erroneousReference.simpleName shouldBe "Bla"
                }
        }

        "duplicate type parameters" {
            validateModule("""
                class Test<T, T> {}
            """.trimIndent())
                .shouldReport<TypeParameterNameConflictReporting>()
        }

        "type parameter name clashes with top level type" {
            validateModule("""
                class Test<Int> {}
            """.trimIndent())
                .shouldReport<TypeParameterNameConflictReporting>()
        }

        "member functions cannot re-declare type parameters declared on class level" {
            validateModule("""
                class Test<T> {
                    fun foo<T>() {}
                }
            """.trimIndent())
                .shouldReport<TypeParameterNameConflictReporting>()
        }
    }

    "supertypes" - {
        "cannot inherit from other class" {
            validateModule("""
                class A {}
                class B : A {}
            """.trimIndent())
                .shouldReport<IllegalSupertypeReporting> {
                    it.supertype.simpleName shouldBe "A"
                }
        }

        "cannot inherit from own type parameter" {
            validateModule("""
                class A<T> : T {}
            """.trimIndent())
                .shouldReport<IllegalSupertypeReporting> {
                    it.supertype.simpleName shouldBe "T"
                }
        }

        "duplicate inheritance from same base type" {
            validateModule("""
                interface A {}
                class B : A, A {}
            """.trimIndent())
                .shouldReport<DuplicateSupertypeReporting> {
                    it.supertype.simpleName shouldBe "A"
                }
        }

        "unknown supertype" {
            validateModule("""
                class Test : Foo {}
            """.trimIndent())
                .shouldReport<UnknownTypeReporting> {
                    it.erroneousReference.simpleName shouldBe "Foo"
                }
        }

        "supertype with type argument out of bounds".config(enabled = false) {
            // TODO: enable once inheriting with generics is implements
            validateModule("""
                interface A {}
                interface Foo<T : A> {}
                class Test : Foo<String> {}
            """.trimIndent())
                .shouldReport<TypeArgumentOutOfBoundsReporting> {
                    it.argument.simpleName shouldBe "String"
                }
        }
    }

    "overriding" - {
        "static functions cannot override" {
            validateModule("""
                interface I {
                    fun foo()
                }
                class C : I {
                    override fun foo()
                }
            """.trimIndent())
                .shouldReport<StaticFunctionDeclaredOverrideReporting>()
        }

        "override must be declared" {
            validateModule("""
                interface I {
                    fun foo(self)
                }
                class C : I {
                    fun foo(self) {
                    }
                }
            """.trimIndent())
                .shouldReport<UndeclaredOverrideReporting>()
                // this could happen if the inherited and the subtype-declared function are considered different
                // and thus clash in the overload-set
                .shouldNotReport<OverloadSetHasNoDisjointParameterReporting>()
        }

        "actually overrides nothing" {
            validateModule("""
                interface I {
                    fun foo(self, p: Int)
                }
                class C : I {
                    override fun foo(self, p: String) {
                    }
                }
            """.trimIndent())
                .shouldReport<SuperFunctionForOverrideNotFoundReporting>()
        }

        "parameter type widening is ambiguous" {
            validateModule("""
                interface I {
                    fun foo(self, p1: Int)
                    fun foo(self, p1: uword)
                }
                class C : I {
                    override fun foo(self, p1: Any) {}
                }
            """.trimIndent())
                .shouldReport<AmbiguousFunctionOverrideReporting>()
        }

        "return type not compatible" {
            validateModule("""
                interface I {
                    fun foo(self) -> Int
                }
                class C : I {
                    override fun foo(self) -> String {
                        return ""
                    }
                }
            """.trimIndent())
                .shouldReport<IncompatibleReturnTypeOnOverrideReporting>()
        }

        "overriding function cannot have more side-effects" {
            validateModule("""
                interface I {
                    fun foo(self) -> Int
                }
                class C : I {
                    override readonly fun foo(self) -> Int = 3
                }
            """.trimIndent())
                .shouldReport<Reporting> {
                    fail("implement")
                }
        }
    }
})