package compiler.compiler.negative

import compiler.reportings.ExplicitInferTypeWithArgumentsReporting
import compiler.reportings.TypeDeductionErrorReporting
import io.kotest.core.spec.style.FreeSpec

class TypeInferenceErrors : FreeSpec({
    "cyclic inference in variables (2)" {
        validateModule("""
            x = y
            y = x
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "cyclic inference in variables (3)" {
        validateModule("""
            x = y
            y = z
            z = x
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
            x = y
            y = a()
            fun a() = z
            z = x
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "cannot infer for variable without initializer expression" {
        validateModule("""
            fun foo() {
                x: _
            }
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "explicit inference type cannot have parameters" {
        validateModule("""
            struct S<T> {}
            fun foo() {
                x: _<Int> = S()
            }
        """.trimIndent())
            .shouldReport<ExplicitInferTypeWithArgumentsReporting>()
    }
})