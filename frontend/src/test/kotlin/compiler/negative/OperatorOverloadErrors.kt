package compiler.compiler.negative

import compiler.reportings.FunctionMissingModifierReporting
import compiler.reportings.OperatorNotDeclaredReporting
import compiler.reportings.UnresolvableFunctionOverloadReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class OperatorOverloadErrors : FreeSpec({
    "unary minus not declared" {
        validateModule("""
            fn foo() {
                a = - false
            }
        """.trimIndent())
            .shouldReport<OperatorNotDeclaredReporting>()
    }

    "binary plus not declared" {
        validateModule("""
            fn foo() {
                a = false + true
            }
        """.trimIndent())
            .shouldReport<UnresolvableFunctionOverloadReporting>()
    }

    "unary minus declared without operator modifier" {
        validateModule("""
            intrinsic fn unaryMinus(self: Bool) -> Bool
            fn foo() {
                x = -false
            }
        """.trimIndent())
            .shouldReport<FunctionMissingModifierReporting> {
                it.function.name shouldBe "unaryMinus"
                it.missingAttribute shouldBe "operator"
            }
    }
})