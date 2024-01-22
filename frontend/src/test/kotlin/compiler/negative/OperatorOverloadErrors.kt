package compiler.compiler.negative

import compiler.ast.type.FunctionModifier
import compiler.reportings.FunctionMissingModifierReporting
import compiler.reportings.OperatorNotDeclaredReporting
import compiler.reportings.UnresolvableFunctionOverloadReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class OperatorOverloadErrors : FreeSpec({
    "unary minus not declared" {
        validateModule("""
            fun foo() {
                val a = - false
            }
        """.trimIndent())
            .shouldReport<OperatorNotDeclaredReporting>()
    }

    "binary plus not declared" {
        validateModule("""
            fun foo() {
                val a = false + true
            }
        """.trimIndent())
            .shouldReport<UnresolvableFunctionOverloadReporting>()
    }

    "unary minus declared without operator modifier" {
        validateModule("""
            external fun unaryMinus(self: Boolean) -> Boolean
            fun foo() {
                val x = -false
            }
        """.trimIndent())
            .shouldReport<FunctionMissingModifierReporting> {
                it.function.name shouldBe "unaryMinus"
                it.missingModifier shouldBe FunctionModifier.Operator
            }
    }
})