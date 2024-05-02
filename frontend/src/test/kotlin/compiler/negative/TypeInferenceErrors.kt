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
            fn a() = b()
            fn b() = a()
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "cyclic inference in variables and functions (mixed)" {
        validateModule("""
            x = y
            y = a()
            fn a() = z
            z = x
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "cannot infer for variable without initializer expression" {
        validateModule("""
            fn foo() {
                x: _
            }
        """.trimIndent())
            .shouldReport<TypeDeductionErrorReporting>()
    }

    "explicit inference type cannot have parameters" {
        validateModule("""
            class S<T> {}
            fn foo() {
                x: _<S32> = S()
            }
        """.trimIndent())
            .shouldReport<ExplicitInferTypeWithArgumentsReporting>()
    }
})