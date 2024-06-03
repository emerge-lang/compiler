package compiler.compiler.parser.grammar.rule

import compiler.compiler.MockEOIToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.matchAgainst
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forAll
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class EitherOfRuleTest : FreeSpec({
    "minimal" - {
        "first" {
            val grammar = eitherOf {
                keyword(Keyword.INTRINSIC)
                keyword(Keyword.OPERATOR)
            }

            val result = matchAgainst(arrayOf(KeywordToken(Keyword.INTRINSIC)), grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<Any>>()
            result.item shouldBe KeywordToken(Keyword.INTRINSIC)
        }

        "second" {
            val grammar = eitherOf {
                keyword(Keyword.INTRINSIC)
                keyword(Keyword.OPERATOR)
            }

            val result = matchAgainst(arrayOf(KeywordToken(Keyword.OPERATOR)), grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<Any>>()
            result.item shouldBe KeywordToken(Keyword.OPERATOR)
        }
    }

    "finds right option on equal length unambiguous alternatives" {
        val grammar = eitherOf {
            sequence {
                keyword(Keyword.IF)
                keyword(Keyword.ELSE)
            }
            sequence {
                keyword(Keyword.IMPORT)
                keyword(Keyword.EXPORT)
            }
        }.flatten().astTransformation { it.remainingToList() }

        val result = matchAgainst(arrayOf(KeywordToken(Keyword.IF), KeywordToken(Keyword.ELSE)), grammar)

        result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
        result.item shouldBe listOf(
            KeywordToken(Keyword.IF),
            KeywordToken(Keyword.ELSE),
        )
    }

    "finds right option when longer alternative breaks" {
        val grammar = eitherOf {
            sequence {
                keyword(Keyword.IF)
                keyword(Keyword.ELSE)
            }
            sequence {
                keyword(Keyword.IF)
                keyword(Keyword.ELSE)
                keyword(Keyword.CLASS_DEFINITION)
            }
        }.flatten().astTransformation { it.remainingToList() }

        val result = matchAgainst(arrayOf(KeywordToken(Keyword.IF), KeywordToken(Keyword.ELSE), MockEOIToken), grammar)

        result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
        result.item shouldBe listOf(
            KeywordToken(Keyword.IF),
            KeywordToken(Keyword.ELSE),
        )
    }

    "finds right option when shorter alternative breaks" {
        val grammar = eitherOf {
            sequence {
                keyword(Keyword.IF)
                keyword(Keyword.ELSE)
            }
            sequence {
                keyword(Keyword.IF)
                keyword(Keyword.EXPORT)
                keyword(Keyword.CLASS_DEFINITION)
            }
        }.flatten().astTransformation { it.remainingToList() }

        val result = matchAgainst(arrayOf(
            KeywordToken(Keyword.IF),
            KeywordToken(Keyword.EXPORT),
            KeywordToken(Keyword.CLASS_DEFINITION),
        ), grammar)

        result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
        result.item shouldBe listOf(
            KeywordToken(Keyword.IF),
            KeywordToken(Keyword.EXPORT),
            KeywordToken(Keyword.CLASS_DEFINITION),
        )
    }

    "given one alternative is a prefix of the other, picks the longer one" {
        val grammar = sequence {
            eitherOf {
                sequence {
                    keyword(Keyword.IF)
                    keyword(Keyword.ELSE)
                }
                sequence {
                    keyword(Keyword.IF)
                    keyword(Keyword.ELSE)
                    keyword(Keyword.CLASS_DEFINITION)
                }
            }
            endOfInput()
        }.flatten().astTransformation { it.remainingToList() }

        val result = matchAgainst(arrayOf(
            KeywordToken(Keyword.IF),
            KeywordToken(Keyword.ELSE),
            KeywordToken(Keyword.CLASS_DEFINITION),
            MockEOIToken,
        ), grammar)

        result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
        result.item shouldBe listOf(
            KeywordToken(Keyword.IF),
            KeywordToken(Keyword.ELSE),
            KeywordToken(Keyword.CLASS_DEFINITION),
        )
    }

    "will continue twice on completely ambiguous input" {
        val grammar = eitherOf {
            keyword(Keyword.IF)
            keyword(Keyword.IF)
        }

        grammar.match(arrayOf(KeywordToken(Keyword.IF)), 0).forAll {
            it.shouldBeInstanceOf<MatchingResult.Success<Any>>()
            it.item shouldBe KeywordToken(Keyword.IF)
        }
    }
})