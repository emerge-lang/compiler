package compiler.compiler.parser.grammar.rule

import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.matchAgainst
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class SequenceRuleTest : FreeSpec({
    "fail on first token" {
        val grammar = sequence {
            keyword(Keyword.IF)
            keyword(Keyword.SET)
        }

        val result = matchAgainst(arrayOf(KeywordToken(Keyword.CLASS_DEFINITION)), grammar)

        result.shouldBeInstanceOf<MatchingResult.Error>()
        result.diagnostic.expectedAlternatives shouldBe setOf("keyword if")
    }

    "fail on middle token" {
        val grammar = sequence {
            keyword(Keyword.IF)
            keyword(Keyword.SET)
            keyword(Keyword.ELSE)
        }

        val result = matchAgainst(arrayOf(
            KeywordToken(Keyword.IF),
            KeywordToken(Keyword.CLASS_DEFINITION),
        ), grammar)

        result.shouldBeInstanceOf<MatchingResult.Error>()
        result.diagnostic.expectedAlternatives shouldBe setOf("keyword set")
    }

    "fail on last token" {
        val grammar = sequence {
            keyword(Keyword.IF)
            keyword(Keyword.SET)
        }

        val result = matchAgainst(arrayOf(
            KeywordToken(Keyword.IF),
            KeywordToken(Keyword.CLASS_DEFINITION),
        ), grammar)

        result.shouldBeInstanceOf<MatchingResult.Error>()
        result.diagnostic.expectedAlternatives shouldBe setOf("keyword set")
    }
})