package compiler.parser

import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.negative.lexCode
import compiler.negative.shouldReport
import compiler.parser.grammar.dsl.*
import compiler.reportings.ParsingMismatchReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.beEmpty
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class MismatchAmbiguityResolutionTest : FreeSpec({
    "sequence backtracking" - {
        val grammar = sequence {
            keyword(Keyword.EXTERNAL)
            eitherOf {
                sequence {
                    keyword(Keyword.OPERATOR)
                    keyword(Keyword.NOTHROW)
                    keyword(Keyword.FUNCTION)
                }
                sequence {
                    keyword(Keyword.OPERATOR)
                    keyword(Keyword.READONLY)
                    keyword(Keyword.VAL)
                }
            }
        }.flatten().mapResult { it.remainingToList() }

        "match first path" {
            val tokens = lexCode("external operator nothrow fun", addModuleDeclaration = false)
            val result = grammar.tryMatch(Unit, tokens)

            result.item.shouldBeInstanceOf<List<out Any>>()
            (result.item as List<out Any>)[0] shouldBe KeywordToken(Keyword.EXTERNAL)
            (result.item as List<out Any>)[1] shouldBe KeywordToken(Keyword.OPERATOR)
            (result.item as List<out Any>)[2] shouldBe KeywordToken(Keyword.NOTHROW)
            (result.item as List<out Any>)[3] shouldBe KeywordToken(Keyword.FUNCTION)
            result.reportings should beEmpty()
            result.isAmbiguous shouldBe false
        }

        "match second path with backtracing" {
            val tokens = lexCode("external operator readonly val", addModuleDeclaration = false)
            val result = grammar.tryMatch(Unit, tokens)

            result.item.shouldBeInstanceOf<List<out Any>>()
            (result.item as List<out Any>)[0] shouldBe KeywordToken(Keyword.EXTERNAL)
            (result.item as List<out Any>)[1] shouldBe KeywordToken(Keyword.OPERATOR)
            (result.item as List<out Any>)[2] shouldBe KeywordToken(Keyword.READONLY)
            (result.item as List<out Any>)[3] shouldBe KeywordToken(Keyword.VAL)
            result.reportings should beEmpty()
            result.isAmbiguous shouldBe false
        }

        "mismatch on ambiguous token" {
            val tokens = lexCode("external operator pure fun", addModuleDeclaration = false)
            val result = grammar.tryMatch(Unit, tokens)

            result.item shouldBe null
            result.isAmbiguous shouldBe true
            result.reportings.shouldReport<ParsingMismatchReporting>()
        }

        "mismatch after disambiguifying token in first branch" {
            val tokens = lexCode("external operator nothrow struct", addModuleDeclaration = false)
            val result = grammar.tryMatch(Unit, tokens)

            result.item shouldBe null
            result.isAmbiguous shouldBe false
            result.reportings.shouldReport<ParsingMismatchReporting> {
                it.expected shouldBe "keyword fun"
                it.actual shouldBe "keyword struct"
            }
        }

        "mismatch after disambiguifying token in second branch" {
            val tokens = lexCode("external operator readonly struct", addModuleDeclaration = false)
            val result = grammar.tryMatch(Unit, tokens)

            result.item shouldBe null
            result.isAmbiguous shouldBe false
            result.reportings.shouldReport<ParsingMismatchReporting> {
                it.expected shouldBe "keyword val"
                it.actual shouldBe "keyword struct"
            }
        }

        "fail before ambiguity in outer sequence" {
            val tokens = lexCode("foo", addModuleDeclaration = false)
            val result = grammar.tryMatch(Unit, tokens)

            result.reportings.shouldReport<ParsingMismatchReporting> {
                it.expected shouldBe "keyword external"
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
            val tokens = lexCode("b e", addModuleDeclaration = false)
            val result = grammar.tryMatch(Unit, tokens)

            result.reportings should beEmpty()
            result.isAmbiguous shouldBe false
            result.item shouldBe listOf(
                IdentifierToken("b"),
                IdentifierToken("e"),
            )
        }

        "mismatch in unambiguous branch should prevent backtracking" {
            val tokens = lexCode("c a", addModuleDeclaration = false)
            val result = grammar.tryMatch(Unit, tokens)

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

            val tokens = lexCode("preA b", addModuleDeclaration = false)
            val result = grammar.tryMatch(Unit, tokens)

            result.reportings should beEmpty()
            result.item shouldBe listOf(
                IdentifierToken("preA"),
                IdentifierToken("b"),
            )
        }
    }
})

private fun GrammarReceiver.identifier(value: String) {
    tokenEqualTo(IdentifierToken(value))
}