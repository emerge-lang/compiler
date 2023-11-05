package matchers.compiler.negative

import compiler.reportings.IllegalFunctionBodyReporting
import compiler.reportings.MissingParameterTypeReporting
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


})