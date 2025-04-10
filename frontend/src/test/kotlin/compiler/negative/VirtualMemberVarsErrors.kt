package compiler.compiler.negative

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

    /*
    TODO: implement more checks and tests

    getters:
    - must take a single, self argument with read mutability
    - must be pure

    setters:
    - must take a self argument with mut mutability
    - must take EXACTLY ONE additional argument
    - must be pure
    - must return Unit

    cross-cutting:
    - for each virtual member var, there must be AT MOST one getter and AT MOST one setter
    - if both are present, the return type of the getter and the argument type on the setter must be identical

    */
})