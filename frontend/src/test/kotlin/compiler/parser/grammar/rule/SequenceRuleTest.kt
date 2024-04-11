package compiler.compiler.parser.grammar.rule

import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.MatchingContinuation
import compiler.reportings.ParsingMismatchReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class SequenceRuleTest : FreeSpec({
    "fail on first token" {
        val grammar = sequence {
            keyword(Keyword.IF)
            keyword(Keyword.SET)
        }
        val completion = MatchingContinuation.Completion<Any>()
        val matcher = grammar.startMatching(completion)
        matcher.step(KeywordToken(Keyword.CLASS_DEFINITION)) shouldBe false
        completion.isCompleted shouldBe true
        completion.result.reportings should haveSize(1)
        completion.result.reportings.forOne {
            it as ParsingMismatchReporting
            it.expectedAlternatives shouldBe setOf("keyword if")
        }
    }

    "fail on middle token" {
        val grammar = sequence {
            keyword(Keyword.IF)
            keyword(Keyword.SET)
            keyword(Keyword.ELSE)
        }
        val completion = MatchingContinuation.Completion<Any>()
        val matcher = grammar.startMatching(completion)
        matcher.step(KeywordToken(Keyword.IF)) shouldBe true
        val consumesLast = matcher.step(KeywordToken(Keyword.CLASS_DEFINITION))
        consumesLast shouldBe false
        completion.isCompleted shouldBe true
        completion.result.reportings should haveSize(1)
        completion.result.reportings.forOne {
            it as ParsingMismatchReporting
            it.expectedAlternatives shouldBe setOf("keyword set")
        }
    }

    "fail on last token" {
        val grammar = sequence {
            keyword(Keyword.IF)
            keyword(Keyword.SET)
        }
        val completion = MatchingContinuation.Completion<Any>()
        val matcher = grammar.startMatching(completion)
        matcher.step(KeywordToken(Keyword.IF)) shouldBe true
        val consumesLast = matcher.step(KeywordToken(Keyword.CLASS_DEFINITION))
        consumesLast shouldBe false
        completion.isCompleted shouldBe true
        completion.result.reportings should haveSize(1)
        completion.result.reportings.forOne {
            it as ParsingMismatchReporting
            it.expectedAlternatives shouldBe setOf("keyword set")
        }
    }
})