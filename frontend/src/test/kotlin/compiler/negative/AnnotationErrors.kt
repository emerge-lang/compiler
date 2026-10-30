package compiler.compiler.negative

import compiler.diagnostic.DisallowedAnnotationDiagnostic
import compiler.diagnostic.InvalidAnnotationMemberDiagnostic
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.UnresolvableFunctionOverloadDiagnostic
import compiler.diagnostic.ValueNotAnnotatableDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class AnnotationErrors : FreeSpec({
    "mutates or reads global state" {
        for (kw in listOf("mut", "read")) {
            validateModule("""
                intrinsic $kw fn x() -> S32
                #[x()]
                class A {
                }
            """.trimIndent())
                .shouldFind<PurityViolationDiagnostic> {
                    it.boundary.shouldBeInstanceOf<PurityViolationDiagnostic.SideEffectBoundary.Annotation>()
                }
        }
    }

    "recognition" - {
        "base type" - {
            "constructor" {
                validateModule("""
                    #[nonexistent()]
                    class A {}
                """.trimIndent())
                    .shouldFind<UnresolvableFunctionOverloadDiagnostic> {
                        it.functionNameReference.value shouldBe "nonexistent"
                    }
            }

            "member var" {
                validateModule("""
                    class A {
                        #[nonexistent()]
                        var x: S32 = 0
                    }
                """.trimIndent())
                    .shouldFind<UnresolvableFunctionOverloadDiagnostic> {
                        it.functionNameReference.value shouldBe "nonexistent"
                    }
            }

            "member function" {
                validateModule("""
                    class A {
                        #[nonexistent()]
                        fn foo(self) {
                        }
                    }
                """.trimIndent())
                    .shouldFind<UnresolvableFunctionOverloadDiagnostic> {
                        it.functionNameReference.value shouldBe "nonexistent"
                    }
            }

            "static member function" {
                validateModule("""
                    class A {
                        #[nonexistent()]
                        fn foo() {
                        }
                    }
                """.trimIndent())
                    .shouldFind<UnresolvableFunctionOverloadDiagnostic> {
                        it.functionNameReference.value shouldBe "nonexistent"
                    }
            }

            "destructor" {
                validateModule("""
                    class A {
                        #[nonexistent()]
                        destructor {}
                    }
                """.trimIndent())
                    .shouldFind<UnresolvableFunctionOverloadDiagnostic> {
                        it.functionNameReference.value shouldBe "nonexistent"
                    }
            }
        }

        "toplevel" - {
            "function" {
                validateModule("""
                    #[nonexistent()]
                    fn test() {}
                """.trimIndent())
                    .shouldFind<UnresolvableFunctionOverloadDiagnostic> {
                        it.functionNameReference.value shouldBe "nonexistent"
                    }
            }

            "variable" {
                validateModule("""
                    #[nonexistent()]
                    x: S32 = 4
                """.trimIndent())
                    .shouldFind<UnresolvableFunctionOverloadDiagnostic> {
                        it.functionNameReference.value shouldBe "nonexistent"
                    }
            }
        }
    }

    "rejected on nested variable declaration in member var" {
        validateModule("""
                fn valid() -> S32
                fn invalid() -> S32
                
                class A<T> {
                    #[valid()]
                    decorates
                    #[invalid()]
                    foo: T = init
                }
        """.trimIndent())
            .shouldFind<DisallowedAnnotationDiagnostic>()
    }

    "circular reference between toplevel functions" {
        validateModule("""
            #[Annotatable()]
            class SomeAnnotation {}
            
            #[b()]
            fn a() -> const SomeAnnotation = SomeAnnotation()
            
            #[a()]
            fn b() -> const SomeAnnotation = SomeAnnotation()
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }

    "value not annotatable" - {
        "not annotated with Annotatable (direct core scalar)" {
            validateModule("""
                fn a() -> S32 = 0
                #[a()]
                fn b() {}
            """.trimIndent())
                .shouldFind<ValueNotAnnotatableDiagnostic>()
        }

        "not annotated with Annotatable (user-defined class)" {
            validateModule(
                """
                    class A {}
                    #[A()]
                    fn b() {}
            """.trimIndent())
                .shouldFind<ValueNotAnnotatableDiagnostic>()
        }

        "not const" {
            validateModule("""
                #[Annotatable()]
                class A {}
                
                fn someA() -> mut A = A()
                
                #[someA()]
                fn b() {}
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic> {
                    it.sourceType.toString() shouldBe "mut testmodule.A"
                    it.targetType.toString() shouldBe "const Any"
                }
        }
    }

    "invalid annotation member" - {
        "reassignable" {
            validateModule("""
                #[Annotatable()]
                class A {
                    var x = 0
                }
            """.trimIndent())
                .shouldFind<InvalidAnnotationMemberDiagnostic>()
        }

        "non scalar type" {
            validateModule("""
                class A {}
                #[Annotatable()]
                class B {
                    foo: A = A()
                }
            """.trimIndent())
                .shouldFind<InvalidAnnotationMemberDiagnostic>()
        }

        "regression for valid annotation classes" {
            validateModule("""
                #[Annotatable()]
                class A {
                    a: Bool
                    b: S8
                    c: U8
                    d: S16
                    e: U16
                    f: S32
                    g: U32
                    h: S64
                    i: U64
                    j: SWord
                    k: UWord
                    l: F32
                    m: F64
                    l: String
                }
                
                fn someA() -> const A = A()
                
                #[someA()]
                fn foo() {}
            """.trimIndent())
        }

        "ref".config(enabled = false) {
            // disabled because ref is not yet implemented in this branch
            validateModule("""
                #[Annotatable()]
                class A {
                    ref x = 0
                }
            """.trimIndent())
        }
    }
})