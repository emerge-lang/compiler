package compiler.compiler.parser

import compiler.compiler.negative.lexCode
import compiler.compiler.negative.shouldReport
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.grammar.dsl.GrammarReceiver
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.MatchingContext
import compiler.reportings.ParsingMismatchReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.beEmpty
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class MismatchAmbiguityResolutionTest : FreeSpec({
    "sequence backtracking" - {
        val grammar = sequence {
            keyword(Keyword.INTRINSIC)
            eitherOf {
                sequence {
                    keyword(Keyword.OPERATOR)
                    keyword(Keyword.NOTHROW)
                    keyword(Keyword.FUNCTION)
                }
                sequence {
                    keyword(Keyword.OPERATOR)
                    keyword(Keyword.READONLY)
                    keyword(Keyword.VAR)
                }
            }
        }.flatten().mapResult { it.remainingToList() }

        "match first path" {
            val tokens = lexCode("intrinsic operator nothrow fun", addPackageDeclaration = false)
            val result = grammar.match(MatchingContext.None, tokens)

            result.item.shouldBeInstanceOf<List<Any>>()
            (result.item as List<Any>)[0] shouldBe KeywordToken(Keyword.INTRINSIC)
            (result.item as List<Any>)[1] shouldBe KeywordToken(Keyword.OPERATOR)
            (result.item as List<Any>)[2] shouldBe KeywordToken(Keyword.NOTHROW)
            (result.item as List<Any>)[3] shouldBe KeywordToken(Keyword.FUNCTION)
            result.reportings should beEmpty()
            result.isAmbiguous shouldBe false
        }

        "match second path with backtracing" {
            val tokens = lexCode("intrinsic operator readonly var", addPackageDeclaration = false)
            val result = grammar.match(MatchingContext.None, tokens)

            result.item.shouldBeInstanceOf<List<Any>>()
            (result.item as List<Any>)[0] shouldBe KeywordToken(Keyword.INTRINSIC)
            (result.item as List<Any>)[1] shouldBe KeywordToken(Keyword.OPERATOR)
            (result.item as List<Any>)[2] shouldBe KeywordToken(Keyword.READONLY)
            (result.item as List<Any>)[3] shouldBe KeywordToken(Keyword.VAR)
            result.reportings should beEmpty()
            result.isAmbiguous shouldBe false
        }

        "mismatch on ambiguous token" {
            val tokens = lexCode("intrinsic operator pure fun", addPackageDeclaration = false)
            val result = grammar.match(MatchingContext.None, tokens)

            result.item shouldBe null
            result.isAmbiguous shouldBe true
            result.reportings.shouldReport<ParsingMismatchReporting>()
        }

        "mismatch after disambiguifying token in first branch" {
            val tokens = lexCode("intrinsic operator nothrow struct", addPackageDeclaration = false)
            val result = grammar.match(MatchingContext.None, tokens)

            result.item shouldBe null
            result.isAmbiguous shouldBe false
            result.reportings.shouldReport<ParsingMismatchReporting> {
                it.expected shouldBe "keyword fun"
                it.actual shouldBe "keyword struct"
            }
        }

        "mismatch after disambiguifying token in second branch" {
            val tokens = lexCode("intrinsic operator readonly struct", addPackageDeclaration = false)
            val result = grammar.match(MatchingContext.None, tokens)

            result.item shouldBe null
            result.isAmbiguous shouldBe false
            result.reportings.shouldReport<ParsingMismatchReporting> {
                it.expected shouldBe "keyword var"
                it.actual shouldBe "keyword struct"
            }
        }

        "fail before ambiguity in outer sequence" {
            val tokens = lexCode("foo", addPackageDeclaration = false)
            val result = grammar.match(MatchingContext.None, tokens)

            result.reportings.shouldReport<ParsingMismatchReporting> {
                it.expected shouldBe "keyword intrinsic"
                it.actual shouldBe "identifier foo"
            }
        }
    }

    "nested either of" - {
        val grammar = sequence {
            eitherOf {
                sequence {
                    eitherOf {
                        identifier("b")
                        identifier("c")
                    }
                    identifier("d")
                }
                sequence {
                    identifier("b")
                    identifier("e")
                }
            }
        }
            .flatten()
            .mapResult { it.remainingToList() }

        "must not affect other ambiguous branches" {
            val tokens = lexCode("b e", addPackageDeclaration = false)
            val result = grammar.match(MatchingContext.None, tokens)

            result.reportings should beEmpty()
            result.isAmbiguous shouldBe false
            result.item shouldBe listOf(
                IdentifierToken("b"),
                IdentifierToken("e"),
            )
        }

        "mismatch in unambiguous branch should prevent backtracking" {
            val tokens = lexCode("c a", addPackageDeclaration = false)
            val result = grammar.match(MatchingContext.None, tokens)

            result.isAmbiguous shouldBe false
            result.item shouldBe null
            result.reportings.shouldReport<ParsingMismatchReporting> {
                it.expected shouldBe "identifier d"
                it.actual shouldBe "identifier a"
            }
        }
    }

    "optional" - {
        "should recognize ambiguity introduced by optional tokens" {
            val grammar = eitherOf {
                sequence {
                    optional {
                        eitherOf {
                            identifier("preA")
                            identifier("preB")
                        }
                    }
                    identifier("a")
                }
                sequence {
                    optional {
                        eitherOf {
                            identifier("preA")
                            identifier("preC")
                        }
                    }
                    identifier("b")
                }
            }
                .flatten()
                .mapResult { it.remainingToList() }

            val tokens = lexCode("preA b", addPackageDeclaration = false)
            val result = grammar.match(MatchingContext.None, tokens)

            result.reportings should beEmpty()
            result.item shouldBe listOf(
                IdentifierToken("preA"),
                IdentifierToken("b"),
            )
        }
    }

    "totally ambiguous eitherOf should not be re-evaluated on recursion / nesting" {
        val valueExpr = eitherOf("value expression") {
            identifier("literal")
            identifier("identifier")
        }

        val binaryExpr = sequence("binary expression") {
            ref(valueExpr)
            identifier("binary operator")
        }

        val expr = eitherOf("expression") {
            ref(binaryExpr)
            ref(valueExpr)
        }
            .flatten()
            .mapResult { it.remainingToList() }

        val tokens = lexCode("identifier", addPackageDeclaration = false)
        val result = expr.match(MatchingContext.None, tokens)

        result.reportings should beEmpty()
        result.isAmbiguous shouldBe false
        result.item shouldBe listOf(IdentifierToken("identifier"))
    }
})

private fun GrammarReceiver.identifier(value: String) {
    tokenEqualTo(IdentifierToken(value))
}