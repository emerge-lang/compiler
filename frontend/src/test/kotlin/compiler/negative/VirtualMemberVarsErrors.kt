package compiler.compiler.negative

import compiler.diagnostic.ConflictingFunctionModifiersDiagnostic
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
})