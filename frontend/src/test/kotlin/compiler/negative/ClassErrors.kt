package compiler.compiler.negative

import compiler.binding.impurity.ImpureInvocation
import compiler.binding.impurity.ReadingVariableBeyondBoundary
import compiler.binding.impurity.ReassignmentBeyondBoundary
import compiler.diagnostic.AbstractInheritedFunctionNotImplementedDiagnostic
import compiler.diagnostic.ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic
import compiler.diagnostic.ConstructorDeclaredModifyingDiagnostic
import compiler.diagnostic.DuplicateBaseTypeMemberDiagnostic
import compiler.diagnostic.DuplicateSupertypeDiagnostic
import compiler.diagnostic.ExplicitOwnershipNotAllowedDiagnostic
import compiler.diagnostic.ExternalMemberFunctionDiagnostic
import compiler.diagnostic.IllegalAssignmentDiagnostic
import compiler.diagnostic.IllegalFunctionBodyDiagnostic
import compiler.diagnostic.IllegalSupertypeDiagnostic
import compiler.diagnostic.IncompatibleReturnTypeOnOverrideDiagnostic
import compiler.diagnostic.MissingFunctionBodyDiagnostic
import compiler.diagnostic.MultipleClassConstructorsDiagnostic
import compiler.diagnostic.MultipleClassDestructorsDiagnostic
import compiler.diagnostic.NotAllMemberVariablesInitializedDiagnostic
import compiler.diagnostic.OverloadSetHasNoDisjointParameterDiagnostic
import compiler.diagnostic.OverrideAddsSideEffectsDiagnostic
import compiler.diagnostic.OverrideDropsNothrowDiagnostic
import compiler.diagnostic.PurityViolationDiagnostic
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
import io.kotest.matchers.types.shouldBeInstanceOf

class ClassErrors : FreeSpec({
    "duplicate member" {
        validateModule("""
            class X {
                a: S32
                b: S32
                a: Bool
            }
        """.trimIndent())
            .shouldFind<DuplicateBaseTypeMemberDiagnostic> {
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
            .shouldFind<UnknownTypeDiagnostic>()
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
            .shouldFind<ValueNotAssignableDiagnostic>()
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
                .shouldFind<ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic>()
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
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<ReadingVariableBeyondBoundary>()
                    }
            }

            "cannot call read functions" {
                validateModule("""
                    intrinsic read fn bar() -> S32
                    class Foo {
                        x: S32 = bar()
                    }
                """.trimIndent())
                    .shouldFind<PurityViolationDiagnostic> {
                        it.impurity.shouldBeInstanceOf<ImpureInvocation>()
                    }
            }

            // TODO: as soon as there are lambdas, add a test to verify a run { ... } initializer can't write
        }

        "cannot declare ownership" {
            validateModule("""
                class Foo {
                    borrow x: S32
                }
            """.trimIndent())
                .shouldFind<ExplicitOwnershipNotAllowedDiagnostic>()
        }
    }

    "member functions" - {
        "must have a body" {
            validateModule("""
                class Test {
                    fn test(self)
                }
            """.trimIndent())
                .shouldFind<MissingFunctionBodyDiagnostic>()
        }

        "intrinsic must not have a body" {
            validateModule("""
                class Test {
                    intrinsic fn test(self) {}
                }
            """.trimIndent())
                .shouldFind<IllegalFunctionBodyDiagnostic>()
        }

        "cannot be external" - {
            "on class" {
                validateModule("""
                    class Test {
                        external(C) nothrow fn foo()
                    }
                """.trimIndent())
                    .shouldFind<ExternalMemberFunctionDiagnostic>()
            }

            "on interface" {
                validateModule("""
                    interface Test {
                        external(C) nothrow fn foo()
                    }
                """.trimIndent())
                    .shouldFind<ExternalMemberFunctionDiagnostic>()
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
                    .shouldFind<AbstractInheritedFunctionNotImplementedDiagnostic>()
            }

            "two degrees of inheritance" {
                validateModule("""
                    interface Animal {
                        fn makeSound(self)
                    }
                    interface QuadraPede : Animal {}
                    class Dog : QuadraPede {}
                """.trimIndent())
                    .shouldFind<AbstractInheritedFunctionNotImplementedDiagnostic>()
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
                    .shouldFind<OverrideDropsNothrowDiagnostic>()
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
                .shouldFind<MultipleClassConstructorsDiagnostic>()
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
                    .shouldFind<UseOfUninitializedClassMemberVariableDiagnostic> {
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
                    .shouldFind<NotAllMemberVariablesInitializedDiagnostic> {
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
                .shouldFind<ClassMemberVariableNotInitializedDuringObjectConstructionDiagnostic> {
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
                    .shouldFind<UseOfUninitializedClassMemberVariableDiagnostic> {
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
                    .shouldFind<NotAllMemberVariablesInitializedDiagnostic> {
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
                        .shouldFind<IllegalAssignmentDiagnostic>()

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
                        .shouldFind<IllegalAssignmentDiagnostic>()
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
                    .shouldFind<IllegalAssignmentDiagnostic>()
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
                    .shouldFind<IllegalAssignmentDiagnostic>()
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
                        .shouldFind<PurityViolationDiagnostic> {
                            it.impurity.shouldBeInstanceOf<ReadingVariableBeyondBoundary>()
                        }
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
                        .shouldFind<PurityViolationDiagnostic> {
                            it.impurity.shouldBeInstanceOf<ReassignmentBeyondBoundary>()
                        }
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
                        .shouldFind<PurityViolationDiagnostic> {
                            it.impurity.shouldBeInstanceOf<ReassignmentBeyondBoundary>()
                        }
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
                    .shouldFind<ConstructorDeclaredModifyingDiagnostic>()
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
                .shouldFind<UndefinedIdentifierDiagnostic> {
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
                .shouldFind<MultipleClassDestructorsDiagnostic>()
        }
    }

    "generics" - {
        "type parameter with unresolvable bound" {
            validateModule("""
                class X<T : Bla> {}
            """.trimIndent())
                .shouldFind<UnknownTypeDiagnostic> {
                    it.erroneousReference.simpleName shouldBe "Bla"
                }
        }

        "duplicate type parameters" {
            validateModule("""
                class Test<T, T> {}
            """.trimIndent())
                .shouldFind<TypeParameterNameConflictDiagnostic>()
        }

        "type parameter name clashes with top level type" {
            validateModule("""
                class Test<S32> {}
            """.trimIndent())
                .shouldFind<TypeParameterNameConflictDiagnostic>()
        }

        "member functions cannot re-declare type parameters declared on class level" {
            validateModule("""
                class Test<T> {
                    fn foo<T>() {}
                }
            """.trimIndent())
                .shouldFind<TypeParameterNameConflictDiagnostic>()
        }
    }

    "supertypes" - {
        "cannot inherit from other class" {
            validateModule("""
                class A {}
                class B : A {}
            """.trimIndent())
                .shouldFind<IllegalSupertypeDiagnostic> {
                    it.supertype.simpleName shouldBe "A"
                }
        }

        "cannot inherit from own type parameter" {
            validateModule("""
                class A<T> : T {}
            """.trimIndent())
                .shouldFind<IllegalSupertypeDiagnostic> {
                    it.supertype.simpleName shouldBe "T"
                }
        }

        "duplicate inheritance from same base type" {
            validateModule("""
                interface A {}
                class B : A, A {}
            """.trimIndent())
                .shouldFind<DuplicateSupertypeDiagnostic> {
                    it.supertype.simpleName shouldBe "A"
                }
        }

        "unknown supertype" {
            validateModule("""
                class Test : Foo {}
            """.trimIndent())
                .shouldFind<UnknownTypeDiagnostic> {
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
                .shouldFind<TypeArgumentOutOfBoundsDiagnostic> {
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
                .shouldFind<StaticFunctionDeclaredOverrideDiagnostic>()
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
                .shouldFind<UndeclaredOverrideDiagnostic>()
                // this could happen if the inherited and the subtype-declared function are considered different
                // and thus clash in the overload-set
                .shouldNotFind<OverloadSetHasNoDisjointParameterDiagnostic>()
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
                .shouldFind<SuperFunctionForOverrideNotFoundDiagnostic>()
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
                .shouldFind<SuperFunctionForOverrideNotFoundDiagnostic>()
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
                .shouldFind<IncompatibleReturnTypeOnOverrideDiagnostic>()
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
                .shouldFind<OverrideAddsSideEffectsDiagnostic>()
        }
    }
})