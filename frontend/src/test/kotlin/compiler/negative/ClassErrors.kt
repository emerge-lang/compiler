package compiler.compiler.negative

import compiler.diagnostic.AbstractInheritedFunctionNotImplementedDiagnostic
import compiler.diagnostic.AssignmentOutsideOfPurityBoundaryDiagnostic
import compiler.diagnostic.ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic
import compiler.diagnostic.ConstructorDeclaredModifyingDiagnostic
import compiler.diagnostic.DuplicateBaseTypeMemberDiagnostic
import compiler.diagnostic.DuplicateSupertypeDiagnostic
import compiler.diagnostic.ExplicitOwnershipNotAllowedDiagnostic
import compiler.diagnostic.ExternalMemberFunctionDiagnostic
import compiler.diagnostic.IllegalAssignmentDiagnostic
import compiler.diagnostic.IllegalFunctionBodyDiagnostic
import compiler.diagnostic.IllegalSupertypeDiagnostic
import compiler.diagnostic.ImpureInvocationInPureContextDiagnostic
import compiler.diagnostic.IncompatibleReturnTypeOnOverrideDiagnostic
import compiler.diagnostic.MissingFunctionBodyDiagnostic
import compiler.diagnostic.MultipleClassConstructorsDiagnostic
import compiler.diagnostic.MultipleClassDestructorsDiagnostic
import compiler.diagnostic.NotAllMemberVariablesInitializedDiagnostic
import compiler.diagnostic.OverloadSetHasNoDisjointParameterDiagnostic
import compiler.diagnostic.OverrideAddsSideEffectsDiagnostic
import compiler.diagnostic.OverrideDropsNothrowDiagnostic
import compiler.diagnostic.ReadInPureContextDiagnostic
import compiler.diagnostic.StaticFunctionDeclaredOverrideDiagnostic
import compiler.diagnostic.SuperFunctionForOverrideNotFoundDiagnostic
import compiler.diagnostic.TypeArgumentOutOfBoundsDiagnostic
import compiler.diagnostic.TypeParameterNameConflictDiagnostic
import compiler.diagnostic.UndeclaredOverrideDiagnostic
import compiler.diagnostic.UndefinedIdentifierDiagnostic
import compiler.diagnostic.UnknownTypeDiagnostic
import compiler.diagnostic.UseOfUninitializedClassMemberVariableDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forAll
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.collections.shouldBeSingleton
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class ClassErrors : FreeSpec({
    "duplicate member" {
        validateModule("""
            class X {
                a: S32
                b: S32
                a: Bool
            }
        """.trimIndent())
            .shouldReport<DuplicateBaseTypeMemberDiagnostic> {
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
            .shouldReport<UnknownTypeDiagnostic>()
    }

    "calling a constructor with incorrect argument types" {
        validateModule("""
            class X {
                a: S32 = init
            }
            
            fn foo() {
                x = X(true)
            }
        """.trimIndent())
            .shouldReport<ValueNotAssignableDiagnostic>()
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
                    x: S32
                }
            """.trimIndent())
                .shouldReport<ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic>()
        }

        "members can be initialized in the custom constructor by assignment" {
            validateModule("""
                class Foo {
                    x: S32
                    
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
                    var x: S32 = 3
                    class Foo {
                        y: S32 = x
                    }
                """.trimIndent())
                    .shouldReport<ReadInPureContextDiagnostic>()
            }

            "cannot call read functions" {
                validateModule("""
                    intrinsic read fn bar() -> S32
                    class Foo {
                        x: S32 = bar()
                    }
                """.trimIndent())
                    .shouldReport<ImpureInvocationInPureContextDiagnostic>()
            }

            // TODO: as soon as there are lambdas, add a test to verify a run { ... } initializer can't write
        }

        "cannot declare ownership" {
            validateModule("""
                class Foo {
                    borrow x: S32
                }
            """.trimIndent())
                .shouldReport<ExplicitOwnershipNotAllowedDiagnostic>()
        }
    }

    "member functions" - {
        "must have a body" {
            validateModule("""
                class Test {
                    fn test(self)
                }
            """.trimIndent())
                .shouldReport<MissingFunctionBodyDiagnostic>()
        }

        "intrinsic must not have a body" {
            validateModule("""
                class Test {
                    intrinsic fn test(self) {}
                }
            """.trimIndent())
                .shouldReport<IllegalFunctionBodyDiagnostic>()
        }

        "cannot be external" - {
            "on class" {
                validateModule("""
                    class Test {
                        external(C) nothrow fn foo()
                    }
                """.trimIndent())
                    .shouldReport<ExternalMemberFunctionDiagnostic>()
            }

            "on interface" {
                validateModule("""
                    interface Test {
                        external(C) nothrow fn foo()
                    }
                """.trimIndent())
                    .shouldReport<ExternalMemberFunctionDiagnostic>()
            }
        }

        "must implement all abstract supertype functions" - {
            "single degree of inheritance" {
                validateModule("""
                    interface Animal {
                        fn makeSound(self)
                    }
                    class Dog : Animal {}
                """.trimIndent())
                    .shouldReport<AbstractInheritedFunctionNotImplementedDiagnostic>()
            }

            "two degrees of inheritance" {
                validateModule("""
                    interface Animal {
                        fn makeSound(self)
                    }
                    interface QuadraPede : Animal {}
                    class Dog : QuadraPede {}
                """.trimIndent())
                    .shouldReport<AbstractInheritedFunctionNotImplementedDiagnostic>()
            }
        }

        "overriding X nothrow" - {
            "if super fn is nothrow, override must be nothrow, too" {
                validateModule("""
                    interface I {
                        nothrow fn foo(self)
                    }
                    class Test : I {
                        override fn foo(self) {}
                    }
                """.trimIndent())
                    .shouldReport<OverrideDropsNothrowDiagnostic>()
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
                .shouldReport<MultipleClassConstructorsDiagnostic>()
        }

        "member variable uninitialized" - {
            "constructor cannot use that member variable" {
                validateModule("""
                    class Foo {
                        x: S32
                        y: S32 = 2
                        
                        constructor {
                            doSomething(self.y)
                            doSomething(self.x)
                            set self.x = 3
                            doSomething(self.x)
                        }
                    }
                    
                    fn doSomething(p: S32) {}
                """.trimIndent())
                    .shouldReport<UseOfUninitializedClassMemberVariableDiagnostic> {
                        it.member.name.value shouldBe "x"
                    }
            }

            "constructor cannot use self" {
                validateModule("""
                    class Foo {
                        x: S32
                        y: S32 = 2
                        
                        constructor {
                            doSomething(self)
                            set self.x = 3
                            doSomething(self)
                        }
                    }
                    
                    fn doSomething(p: Foo) {}
                """.trimIndent())
                    .shouldReport<NotAllMemberVariablesInitializedDiagnostic> {
                        it.uninitializedMembers.shouldBeSingleton().single().name.value shouldBe "x"
                    }
            }
        }

        "constructor must initialize all member variables" {
            validateModule("""
                class Foo {
                    x: S32
                    y: S32
                    
                    constructor {
                        set self.x = 1
                    }
                }
            """.trimIndent())
                .shouldReport<ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic> {
                    it.memberDeclaration.name.value shouldBe "y"
                }
        }

        "member variable has maybe been initialized" - {
            "constructor cannot use that member variable" {
                validateModule("""
                    class Foo {
                        cond: Bool = init
                        x: S32
                        
                        constructor {
                            if self.cond {
                                set self.x = 3
                            }
                            doSomething(self.x)
                        }
                    }
                    
                    fn doSomething(p: S32) {}
                """.trimIndent())
                    .shouldReport<UseOfUninitializedClassMemberVariableDiagnostic> {
                        it.member.name.value shouldBe "x"
                    }
            }

            "constructor cannot use self" {
                validateModule("""
                    class Foo {
                        cond: Bool = init
                        x: S32
                        
                        constructor {
                            if self.cond {
                                set self.x = 3
                            }
                            doSomething(self)
                        }
                    }
                    
                    fn doSomething(p: Foo) {}
                """.trimIndent())
                    .shouldReport<NotAllMemberVariablesInitializedDiagnostic> {
                        it.uninitializedMembers should haveSize(1)
                        it.uninitializedMembers.single().name.value shouldBe "x"
                    }
            }

            "interaction with while loops" - {
                "cannot initialize single-assignment variable in loop" {
                    validateModule("""
                        class Foo {
                            x: S32
                            read constructor {
                                while random() {
                                    set self.x = 5
                                }
                            }
                        }
                        read intrinsic fn random() -> Bool
                    """.trimIndent())
                        .shouldReport<IllegalAssignmentDiagnostic>()

                    validateModule("""
                        class Foo {
                            x: S32
                            read constructor {
                                while random() {
                                    y = 3
                                    set self.x = 5
                                }
                            }
                        }
                        read intrinsic fn random() -> Bool
                    """.trimIndent())
                        .shouldReport<IllegalAssignmentDiagnostic>()
                }

                "execution uncertainty of loops doesn't persist to code after the loop" {
                    validateModule("""
                        class Foo {
                            x: S32
                            read constructor {
                                while random() {
                                    unrelated = 3
                                }
                                set self.x = 5
                                y = self.x
                            }
                        }
                        read intrinsic fn random() -> Bool
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }
            }
        }

        "member variable has been initialized in two different ways" - {
            "constructor can use that member variable" {
                validateModule("""
                    class Foo {
                        cond: Bool = init
                        x: S32
                        
                        constructor {
                            if self.cond {
                                set self.x = 3
                            } else {
                                set self.x = 4
                            }
                            doSomething(self.x)
                        }
                    }
                    
                    fn doSomething(p: S32) {}
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "constructor can use self" {
                validateModule("""
                    class Foo {
                        cond: Bool = init
                        x: S32
                        
                        constructor {
                            if self.cond {
                                set self.x = 3
                            } else {
                                set self.x = 4
                            }
                            doSomething(self)
                        }
                    }
                    
                    fn doSomething(borrow p: Foo) {}
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }
        }

        "single-assignment member variable" - {
            "assigned twice linearly" {
                validateModule("""
                    class Foo {
                        x: S32
                        constructor {
                            set self.x = 1
                            set self.x = 2
                        }
                    }
                """.trimIndent())
                    .shouldReport<IllegalAssignmentDiagnostic>()
            }

            "assigned in a loop" {
                validateModule("""
                    class Foo {
                        x: S32
                        read constructor {
                            while random() {
                                set self.x = 3
                            }
                        }
                    }
                    read intrinsic fn random() -> Bool
                """.trimIndent())
                    .shouldReport<IllegalAssignmentDiagnostic>()
            }
        }

        "purity" - {
            "constructor is pure by default" - {
                "cannot read global state" {
                    validateModule("""
                        intrinsic read fn foo() -> S32
                        x: S32 = foo()
                        class Test {
                            y: S32
                            constructor {
                                set self.y = x
                            }
                        }
                    """.trimIndent())
                        .shouldReport<ReadInPureContextDiagnostic>()
                }

                "cannot write global state" {
                    validateModule("""
                        var x: S32 = 0
                        class Test {
                            constructor {
                                set x = 1
                            }
                        }
                    """.trimIndent())
                        .shouldReport<AssignmentOutsideOfPurityBoundaryDiagnostic>()
                }
            }

            "constructor declared as read" - {
                "can read global state" {
                    validateModule("""
                        intrinsic read fn foo() -> S32
                        x: S32 = foo()
                        class Test {
                            y: S32
                            read constructor {
                                set self.y = x
                            }
                        }
                    """.trimIndent())
                        .shouldHaveNoDiagnostics()
                }

                "cannot write global state" {
                    validateModule("""
                        var x: S32 = 0
                        class Test {
                            read constructor {
                                set x = 1
                            }
                        }
                    """.trimIndent())
                        .shouldReport<AssignmentOutsideOfPurityBoundaryDiagnostic>()
                }
            }

            "constructor cannot be declared modifying" {
                validateModule("""
                    var x = 0
                    class Test {
                        mut constructor {
                            set x = 1
                        }
                    }
                """.trimIndent())
                    .shouldReport<ConstructorDeclaredModifyingDiagnostic>()
            }
        }

        "cannot access generated parameters for init-variables" {
            validateModule("""
                class A {
                    x: String = init
                    y: String
                    constructor {
                        set self.y = x
                    }
                }
            """.trimIndent())
                .shouldReport<UndefinedIdentifierDiagnostic> {
                    it.expr.value shouldBe "x"
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
                .shouldReport<MultipleClassDestructorsDiagnostic>()
        }
    }

    "generics" - {
        "type parameter with unresolvable bound" {
            validateModule("""
                class X<T : Bla> {}
            """.trimIndent())
                .shouldReport<UnknownTypeDiagnostic> {
                    it.erroneousReference.simpleName shouldBe "Bla"
                }
        }

        "duplicate type parameters" {
            validateModule("""
                class Test<T, T> {}
            """.trimIndent())
                .shouldReport<TypeParameterNameConflictDiagnostic>()
        }

        "type parameter name clashes with top level type" {
            validateModule("""
                class Test<S32> {}
            """.trimIndent())
                .shouldReport<TypeParameterNameConflictDiagnostic>()
        }

        "member functions cannot re-declare type parameters declared on class level" {
            validateModule("""
                class Test<T> {
                    fn foo<T>() {}
                }
            """.trimIndent())
                .shouldReport<TypeParameterNameConflictDiagnostic>()
        }
    }

    "supertypes" - {
        "cannot inherit from other class" {
            validateModule("""
                class A {}
                class B : A {}
            """.trimIndent())
                .shouldReport<IllegalSupertypeDiagnostic> {
                    it.supertype.simpleName shouldBe "A"
                }
        }

        "cannot inherit from own type parameter" {
            validateModule("""
                class A<T> : T {}
            """.trimIndent())
                .shouldReport<IllegalSupertypeDiagnostic> {
                    it.supertype.simpleName shouldBe "T"
                }
        }

        "duplicate inheritance from same base type" {
            validateModule("""
                interface A {}
                class B : A, A {}
            """.trimIndent())
                .shouldReport<DuplicateSupertypeDiagnostic> {
                    it.supertype.simpleName shouldBe "A"
                }
        }

        "unknown supertype" {
            validateModule("""
                class Test : Foo {}
            """.trimIndent())
                .shouldReport<UnknownTypeDiagnostic> {
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
                .shouldReport<TypeArgumentOutOfBoundsDiagnostic> {
                    it.argument.simpleName shouldBe "String"
                }
        }
    }

    "overriding" - {
        "static functions cannot override" {
            validateModule("""
                interface I {
                    fn foo()
                }
                class C : I {
                    override fn foo()
                }
            """.trimIndent())
                .shouldReport<StaticFunctionDeclaredOverrideDiagnostic>()
        }

        "override must be declared" {
            validateModule("""
                interface I {
                    fn foo(self)
                }
                class C : I {
                    fn foo(self) {
                    }
                }
            """.trimIndent())
                .shouldReport<UndeclaredOverrideDiagnostic>()
                // this could happen if the inherited and the subtype-declared function are considered different
                // and thus clash in the overload-set
                .shouldNotReport<OverloadSetHasNoDisjointParameterDiagnostic>()
        }

        "actually overrides nothing" {
            validateModule("""
                interface I {
                    fn foo(self, p: S32)
                }
                class C : I {
                    override fn foo(self, p: String) {
                    }
                }
            """.trimIndent())
                .shouldReport<SuperFunctionForOverrideNotFoundDiagnostic>()
        }

        "widening the type of a parameter does not count as overriding" {
            validateModule("""
                interface I {
                    fn foo(self, p1: S32)
                }
                class C : I {
                    override fn foo(self, p1: Any) {}
                }
            """.trimIndent())
                .shouldReport<SuperFunctionForOverrideNotFoundDiagnostic>()
        }

        "return type not compatible" {
            validateModule("""
                interface I {
                    fn foo(self) -> S32
                }
                class C : I {
                    override fn foo(self) -> String {
                        return ""
                    }
                }
            """.trimIndent())
                .shouldReport<IncompatibleReturnTypeOnOverrideDiagnostic>()
        }

        "overriding function cannot have more side-effects" {
            validateModule("""
                interface I {
                    fn foo(self) -> S32
                }
                class C : I {
                    override read fn foo(self) -> S32 = 3
                }
            """.trimIndent())
                .shouldReport<OverrideAddsSideEffectsDiagnostic>()
        }
    }
})