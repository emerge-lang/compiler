package compiler.compiler.negative

import compiler.diagnostic.DisallowedAnnotationDiagnostic
import compiler.diagnostic.PurityViolationDiagnostic
import compiler.diagnostic.UnresolvableFunctionOverloadDiagnostic
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
            #[b()]
            fn a() {}
            
            #[a()]
            fn b() {}
        """.trimIndent())
            .shouldHaveNoDiagnostics()
    }
})