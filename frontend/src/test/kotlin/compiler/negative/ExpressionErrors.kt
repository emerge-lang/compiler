package compiler.compiler.negative

import compiler.ast.VariableDeclaration
import compiler.binding.expression.BoundIdentifierExpression
import compiler.diagnostic.ImplicitlyEvaluatedStatementDiagnostic
import compiler.diagnostic.UnsafeObjectTraversalDiagnostic
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class ExpressionErrors : FreeSpec({
    "unsafe object traversal" {
        validateModule("""
            class X {
                a: S32 = init
            }
            fn foo(p: X?) -> S32 {
                return p.a
            }
        """.trimIndent())
            .shouldFind<UnsafeObjectTraversalDiagnostic> {
                it.nullableExpression.shouldBeInstanceOf<BoundIdentifierExpression>().identifier shouldBe "p"
            }
    }

    "implicitly evaluating statement" - {
        "return - should not error" {
            validateModule("""
                fn foo() -> S32 {
                    x: Bool = if true {
                        return 3
                    } else {
                        return 2
                    }
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "variable declaration" {
            validateModule("""
                fn foo() {
                    x: Bool = if true {
                        y = 3 
                    } else {
                        false
                    }
                }
            """.trimIndent())
                .shouldFind<ImplicitlyEvaluatedStatementDiagnostic> {
                    it.statement.shouldBeInstanceOf<VariableDeclaration>().name.value shouldBe "y"
                }
        }

        "should error if no implicit evaluation" {
            validateModule("""
                fn foo(cond: Bool) {
                    x: S32 = if cond {
                        3
                    } else {}
                }
            """.trimIndent())
                .shouldFind<ImplicitlyEvaluatedStatementDiagnostic>()
        }
    }
})