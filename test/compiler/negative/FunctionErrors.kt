package matchers.compiler.negative

import compiler.reportings.IllegalFunctionBodyReporting
import compiler.reportings.MissingParameterTypeReporting
import compiler.reportings.ModifierInefficiencyReporting
import compiler.reportings.MultipleParameterDeclarationsReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class FunctionErrors : FreeSpec({
    "external function cannot have body" {
        validateModule("""
            external fun foo() -> Int {
                return 3
            }
        """.trimIndent())
            .shouldReport<IllegalFunctionBodyReporting>()
    }

    "function parameters must have explicit types" {
        validateModule("""
            fun foo(bar) = 3
        """.trimIndent())
            .shouldReport<MissingParameterTypeReporting>() {
                it.parameter.name.value shouldBe "bar"
            }
    }

    "readonly+pure redundancy" {
        validateModule("""
            readonly pure fun foo() {}
        """.trimIndent())
            .shouldReport<ModifierInefficiencyReporting>()
    }

    "parameter name duplicate" {
        validateModule("""
            fun foo(a: Int, a: Boolean, b: Int) {}
        """.trimIndent())
            .shouldReport<MultipleParameterDeclarationsReporting> {
                it.firstDeclaration.name.value shouldBe "a"
                it.additionalDeclaration.name.value shouldBe "a"
            }
    }
})