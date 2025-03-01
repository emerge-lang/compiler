package compiler.compiler.negative

import compiler.diagnostic.ExplicitInferTypeWithArgumentsDiagnostic
import compiler.diagnostic.TypeDeductionErrorDiagnostic
import io.kotest.core.spec.style.FreeSpec

class TypeInferenceErrors : FreeSpec({
    "cyclic inference in variables (2)" {
        validateModule("""
            x = y
            y = x
        """.trimIndent())
            .shouldFind<TypeDeductionErrorDiagnostic>()
    }

    "cyclic inference in variables (3)" {
        validateModule("""
            x = y
            y = z
            z = x
        """.trimIndent())
            .shouldFind<TypeDeductionErrorDiagnostic>()
    }

    "cyclic inference in functions" {
        validateModule("""
            fn a() = b()
            fn b() = a()
        """.trimIndent())
            .shouldFind<TypeDeductionErrorDiagnostic>(allowMultiple = true)
    }

    "cyclic inference in variables and functions (mixed)" {
        validateModule("""
            x = y
            y = a()
            fn a() = z
            z = x
        """.trimIndent())
            .shouldFind<TypeDeductionErrorDiagnostic>()
    }

    "cannot infer for variable without initializer expression" {
        validateModule("""
            fn foo() {
                x: _
            }
        """.trimIndent())
            .shouldFind<TypeDeductionErrorDiagnostic>()
    }

    "explicit inference type cannot have parameters" {
        validateModule("""
            class S<T> {}
            fn foo() {
                x: _<S32> = S()
            }
        """.trimIndent())
            .shouldFind<ExplicitInferTypeWithArgumentsDiagnostic>()
    }
})