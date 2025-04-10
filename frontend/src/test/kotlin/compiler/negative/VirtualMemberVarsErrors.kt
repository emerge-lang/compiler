package compiler.compiler.negative

import compiler.diagnostic.ConflictingFunctionModifiersDiagnostic
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
})