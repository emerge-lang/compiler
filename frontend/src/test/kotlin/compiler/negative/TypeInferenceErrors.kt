package compiler.compiler.negative

import compiler.reportings.ExplicitInferTypeWithArgumentsDiagnostic
import compiler.reportings.TypeDeductionErrorDiagnostic
import io.kotest.core.spec.style.FreeSpec

class TypeInferenceErrors : FreeSpec({
    "cyclic inference in variables (2)" {
        validateModule("""
            x = y
            y = x
        """.trimIndent())
            .shouldReport<TypeDeductionErrorDiagnostic>()
    }

    "cyclic inference in variables (3)" {
        validateModule("""
            x = y
            y = z
            z = x
        """.trimIndent())
            .shouldReport<TypeDeductionErrorDiagnostic>()
    }

    "cyclic inference in functions" {
        validateModule("""
            fn a() = b()
            fn b() = a()
        """.trimIndent())
            .shouldReport<TypeDeductionErrorDiagnostic>()
    }

    "cyclic inference in variables and functions (mixed)" {
        validateModule("""
            x = y
            y = a()
            fn a() = z
            z = x
        """.trimIndent())
            .shouldReport<TypeDeductionErrorDiagnostic>()
    }

    "cannot infer for variable without initializer expression" {
        validateModule("""
            fn foo() {
                x: _
            }
        """.trimIndent())
            .shouldReport<TypeDeductionErrorDiagnostic>()
    }

    "explicit inference type cannot have parameters" {
        validateModule("""
            class S<T> {}
            fn foo() {
                x: _<S32> = S()
            }
        """.trimIndent())
            .shouldReport<ExplicitInferTypeWithArgumentsDiagnostic>()
    }
})