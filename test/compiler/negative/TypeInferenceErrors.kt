package compiler.negative

import compiler.reportings.TypeDeductionErrorReporting
import io.kotest.core.spec.style.FreeSpec

class TypeInferenceErrors : FreeSpec({
    "cyclic inference in variables (2)" {
        validateModule("""
            val x = y
            val y = x
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "cyclic inference in variables (3)" {
        validateModule("""
            val x = y
            val y = z
            val z = x
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "cyclic inference in functions" {
        validateModule("""
            fun a() = b()
            fun b() = a()
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "cyclic inference in variables and functions (mixed)" {
        validateModule("""
            val x = y
            val y = a()
            fun a() = z
            val z = x
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "cannot infer for variable without initializer expression" {
        validateModule("""
            fun foo() {
                val x
            }
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }
})