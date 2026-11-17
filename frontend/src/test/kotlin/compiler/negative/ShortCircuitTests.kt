package compiler.compiler.negative

import compiler.diagnostic.MutationInConditionDiagnostic
import compiler.diagnostic.OperatorNotDeclaredDiagnostic
import compiler.diagnostic.SideEffectInShortCircuitedOperandDiagnostic
import compiler.diagnostic.ValueNotAssignableDiagnostic
import compiler.lexer.Keyword
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class ShortCircuitTests : FreeSpec({
    val declarations = """
        token class Counter {
            var n: S32 = 0
        }
        intrinsic fn modify(borrow c: mut Counter) -> Bool
        intrinsic fn check(borrow c: read Counter) -> Bool
        intrinsic fn mayThrow() -> Bool
    """.trimIndent()

    "operands" - {
        "and/or require Bool on the left-hand side" {
            validateModule("""
                fn test(a: S32, b: Bool) -> Bool = a and b
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "and/or require Bool on the right-hand side" {
            validateModule("""
                fn test(a: Bool, b: S32) -> Bool = a or b
            """.trimIndent())
                .shouldFind<ValueNotAssignableDiagnostic>()
        }

        "&, |, xor and not on integers are bitwise" {
            validateModule("""
                fn test(a: S32, b: S32, c: S32) -> S32 = a & b | c
                fn test2(a: U8) -> U8 = a & 0b00001111
                fn test3(a: S32, b: S32) -> Bool = a xor b == 0
                fn test4(a: S32) -> S32 = not a
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "& and | on Bool" {
            validateModule("""
                fn test(a: Bool, b: Bool, c: Bool) -> Bool = a & b | c
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "& on a type without the operator" {
            validateModule("""
                class Foo {}
                fn test(a: Foo, b: Foo) = a & b
            """.trimIndent())
                .shouldFind<OperatorNotDeclaredDiagnostic>()
        }
    }

    "side effects" - {
        "in the right-hand side of and" {
            validateModule("""
                $declarations
                fn test(p: Bool, borrow c: mut Counter) -> Bool = p and modify(c)
            """.trimIndent())
                .shouldFind<SideEffectInShortCircuitedOperandDiagnostic> {
                    it.operator shouldBe Keyword.AND
                }
        }

        "in the right-hand side of or" {
            validateModule("""
                $declarations
                fn test(p: Bool, borrow c: mut Counter) -> Bool = p or modify(c)
            """.trimIndent())
                .shouldFind<SideEffectInShortCircuitedOperandDiagnostic> {
                    it.operator shouldBe Keyword.OR
                }
        }

        "not in the left-hand side, which is always evaluated" {
            validateModule("""
                $declarations
                fn test(p: Bool, borrow c: mut Counter) -> Bool = modify(c) and p
                fn test2(p: Bool, borrow c: mut Counter) -> Bool = modify(c) or p
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not with & and |, which always evaluate both sides" {
            validateModule("""
                $declarations
                fn test(p: Bool, borrow c: mut Counter) -> Bool = p & modify(c)
                fn test2(p: Bool, borrow c: mut Counter) -> Bool = p | modify(c)
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not for reading" {
            validateModule("""
                $declarations
                fn test(p: Bool, borrow c: mut Counter) -> Bool = p and check(c)
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not for state created in the right-hand side" {
            validateModule("""
                $declarations
                fn test(p: Bool) -> Bool = p and modify(Counter())
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "not for throwing" {
            validateModule("""
                $declarations
                fn test(p: Bool) -> Bool = p and mayThrow()
            """.trimIndent())
                .shouldHaveNoDiagnostics()
        }

        "nested in the right-hand side, reported once" {
            validateModule("""
                $declarations
                fn test(p: Bool, q: Bool, borrow c: mut Counter) -> Bool = p and (q or modify(c))
            """.trimIndent())
                .shouldFind<SideEffectInShortCircuitedOperandDiagnostic> {
                    it.operator shouldBe Keyword.OR
                }
        }

        "in the left-hand side of an and nested in the right-hand side" {
            validateModule("""
                $declarations
                fn test(p: Bool, q: Bool, borrow c: mut Counter) -> Bool = p or (modify(c) and q)
            """.trimIndent())
                .shouldFind<SideEffectInShortCircuitedOperandDiagnostic> {
                    it.operator shouldBe Keyword.OR
                }
        }

        "in a condition" - {
            "in the right-hand side, reported only as such" {
                validateModule("""
                    $declarations
                    fn test(p: Bool, borrow c: mut Counter) {
                        if p and modify(c) {
                        }
                    }
                """.trimIndent())
                    .shouldFind<SideEffectInShortCircuitedOperandDiagnostic>()
                    .shouldNotFind<MutationInConditionDiagnostic>()
            }

            "in the left-hand side, reported as mutation in condition" {
                validateModule("""
                    $declarations
                    fn test(p: Bool, borrow c: mut Counter) {
                        while modify(c) and p {
                        }
                    }
                """.trimIndent())
                    .shouldFind<MutationInConditionDiagnostic>()
                    .shouldNotFind<SideEffectInShortCircuitedOperandDiagnostic>()
            }
        }
    }
})
