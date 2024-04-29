package compiler.compiler.negative

import compiler.ast.VariableDeclaration
import compiler.binding.expression.BoundIdentifierExpression
import compiler.reportings.ImplicitlyEvaluatedStatementReporting
import compiler.reportings.UnsafeObjectTraversalReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class ExpressionErrors : FreeSpec({
    "unsafe object traversal" {
        validateModule("""
            class X {
                a: S32
            }
            fun foo(p: X?) -> S32 {
                return p.a
            }
        """.trimIndent())
            .shouldReport<UnsafeObjectTraversalReporting> {
                it.nullableExpression.shouldBeInstanceOf<BoundIdentifierExpression>().identifier shouldBe "p"
            }
    }

    "implicitly evaluating statement" - {
        "return - should not error" {
            validateModule("""
                fun foo() -> S32 {
                    x: Boolean = if true {
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
                fun foo() {
                    x: Boolean = if true {
                        y = 3 
                    } else {
                        false
                    }
                }
            """.trimIndent())
                .shouldReport<ImplicitlyEvaluatedStatementReporting> {
                    it.statement.shouldBeInstanceOf<VariableDeclaration>().name.value shouldBe "y"
                }
        }
    }
})