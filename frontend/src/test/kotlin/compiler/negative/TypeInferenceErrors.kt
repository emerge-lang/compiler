package compiler.compiler.negative

import compiler.diagnostic.ExplicitInferTypeWithArgumentsDiagnostic
import compiler.diagnostic.ReturnTypeMismatchDiagnostic
import compiler.diagnostic.TypeDeductionErrorDiagnostic
import io.kotest.core.spec.style.FreeSpec

class TypeInferenceErrors : FreeSpec({
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

    "bounds of type variables" - {
        val declarations = """
            interface A {}
            interface B : A {}
            interface C : A {}
            interface E {}
            class Box<T> {
                var value: T = init
            }
            fn pick<X>(a: X, b: X) -> X {
                return a
            }
            fn takeOne<X>(a: Box<in X>) {}
            fn takeTwo<X>(a: Box<in X>, b: Box<in X>) {}
        """.trimIndent()

        "the closest common supertype of an in-variant and an out-variant type argument" - {
            "is out read Any?" {
                validateModule(declarations + "\n" + """
                    fn f(p: Box<in B>, q: Box<out C>) -> Box<out read Any?> {
                        return pick(p, q)
                    }
                """.trimIndent())
                    .shouldHaveNoDiagnostics()
            }

            "reads as nothing closer than read Any?" {
                validateModule(declarations + "\n" + """
                    fn f(p: Box<in B>, q: Box<out C>) -> A {
                        return pick(p, q).value
                    }
                """.trimIndent())
                    .shouldFind<ReturnTypeMismatchDiagnostic>()
            }
        }
    }
})