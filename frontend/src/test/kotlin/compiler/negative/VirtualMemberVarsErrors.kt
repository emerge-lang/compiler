package compiler.compiler.negative

import compiler.diagnostic.AccessorContractViolationDiagnostic
import compiler.diagnostic.ConflictingFunctionModifiersDiagnostic
import compiler.diagnostic.OverrideAccessorDeclarationMismatchDiagnostic
import compiler.diagnostic.VirtualAndActualMemberVariableNameClashDiagnostic
import compiler.lexer.Keyword
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class VirtualMemberVarsErrors : FreeSpec({
    "marking a method both get and set produces a conflict" {
        validateModule("""
            class A {
                get set fn bla(self) -> S32 = 0
            }
        """.trimIndent())
            .shouldFind<ConflictingFunctionModifiersDiagnostic> {
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
                        override set fn bla(self, v: S32) {}
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
                        get fn bla(self, v: S32)
                    }
                    class A : I {
                        override fn bla(self, v: S32) {}
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
    }

    /*
    TODO: implement more checks and tests

    setters:
    - must take a self argument with mut mutability
    - must take EXACTLY ONE additional argument
    - must return Unit

    cross-cutting:
    - for each virtual member var, there must be AT MOST one getter and AT MOST one setter
    - if both are present, the return type of the getter and the argument type on the setter must be identical

    */
})