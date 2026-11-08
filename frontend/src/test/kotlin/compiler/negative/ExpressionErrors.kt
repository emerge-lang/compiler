package compiler.compiler.negative

import compiler.ast.VariableDeclaration
import compiler.binding.expression.BoundIdentifierExpression
import compiler.diagnostic.ImplicitlyEvaluatedStatementDiagnostic
import compiler.diagnostic.PrefixOperatorNeedsParenthesesDiagnostic
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

    "operator precedence" - {
        "prefix operator weaker than enclosing infix operator" {
            validateModule("""
                fn foo(a: Bool, b: Bool) -> Bool {
                    return a == not b
                }
            """.trimIndent())
                .shouldFind<PrefixOperatorNeedsParenthesesDiagnostic> {
                    it.enclosingOperator.name shouldBe "=="
                }
        }

        "prefix operator weaker than enclosing prefix operator" {
            validateModule("""
                fn foo(x: S32) -> S32 {
                    return - not x
                }
            """.trimIndent())
                .shouldFind<PrefixOperatorNeedsParenthesesDiagnostic> {
                    it.enclosingOperator.name shouldBe "-"
                }
        }

        "parenthesised and naturally grouped prefix operators are fine" {
            validateModule("""
                fn foo(a: Bool, b: Bool, x: S32, y: S32) -> Bool {
                    v1 = x == (not y)
                    v2 = not x == y
                    v3 = a and not b
                    v4 = -(not x)
                    v5 = -x * 2 + 20
                    return v1 and v2 and v3
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "xor" {
            validateModule("""
                fn foo(a: Bool, b: Bool, c: Bool) -> Bool {
                    return a xor b and c
                }
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }
    }
})
