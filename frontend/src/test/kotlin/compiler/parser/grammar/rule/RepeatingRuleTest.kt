package compiler.compiler.parser.grammar.rule

import compiler.compiler.MockEOIToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.matchAgainst
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class RepeatingRuleTest : FreeSpec({
    "unbound repeat" - {
        val grammar = sequence {
            repeating {
                keyword(Keyword.IF)
            }
            keyword(Keyword.EXPORT)
        }.flatten().mapResult { it.remainingToList() }

        "accepts zero matches" {
            val result = matchAgainst(arrayOf(KeywordToken(Keyword.EXPORT)), grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
            result.item shouldBe listOf(KeywordToken(Keyword.EXPORT))
        }

        "accepts one match" {
            val result = matchAgainst(arrayOf(
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.EXPORT),
            ), grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
            result.item shouldBe listOf(
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.EXPORT),
            )
        }

        "accepts four matches" {
            val result = matchAgainst(arrayOf(
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.EXPORT),
            ), grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
            result.item shouldBe listOf(
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.EXPORT),
            )
        }
    }

    "optional" - {
        val grammar = sequence {
            optional {
                keyword(Keyword.IF)
            }
            keyword(Keyword.EXPORT)
        }.flatten().mapResult { it.remainingToList() }

        "accepts zero matches" {
            val result = matchAgainst(arrayOf(KeywordToken(Keyword.EXPORT)), grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
            result.item shouldBe listOf(KeywordToken(Keyword.EXPORT))
        }

        "accepts one match" {
            val result = matchAgainst(arrayOf(
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.EXPORT),
            ), grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
            result.item shouldBe listOf(
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.EXPORT),
            )
        }

        "rejects two matches" {
            val grammar = sequence {
                optional {
                    keyword(Keyword.IF)
                }
                keyword(Keyword.EXPORT)
            }.flatten().mapResult { it.remainingToList() }

            val result = matchAgainst(arrayOf(
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.IF),
                MockEOIToken,
            ), grammar)
            result.shouldBeInstanceOf<MatchingResult.Error>()
            result.diagnostic.expectedAlternatives shouldBe listOf("keyword export")
            result.diagnostic.actual shouldBe KeywordToken(Keyword.IF)
        }
    }
})