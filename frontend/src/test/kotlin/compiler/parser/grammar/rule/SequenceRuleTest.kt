package compiler.compiler.parser.grammar.rule

import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Token
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.FirstMatchCompletion
import compiler.parser.grammar.rule.IdentifierTokenRule
import compiler.parser.grammar.rule.MatchingContinuation
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.OngoingMatch
import compiler.parser.grammar.rule.Rule
import compiler.parser.grammar.rule.SequenceRule
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
        val completion = FirstMatchCompletion<Any>()
        val matcher = grammar.startMatching(completion)
        matcher.step(KeywordToken(Keyword.CLASS_DEFINITION)) shouldBe false
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
        val completion = FirstMatchCompletion<Any>()
        val matcher = grammar.startMatching(completion)
        matcher.step(KeywordToken(Keyword.IF)) shouldBe true
        val consumesLast = matcher.step(KeywordToken(Keyword.CLASS_DEFINITION))
        consumesLast shouldBe false
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
        val completion = FirstMatchCompletion<Any>()
        val matcher = grammar.startMatching(completion)
        matcher.step(KeywordToken(Keyword.IF)) shouldBe true
        val consumesLast = matcher.step(KeywordToken(Keyword.CLASS_DEFINITION))
        consumesLast shouldBe false
        completion.result.reportings should haveSize(1)
        completion.result.reportings.forOne {
            it as ParsingMismatchReporting
            it.expectedAlternatives shouldBe setOf("keyword set")
        }
    }

    "continuation is reentrant" {
        val rule = SequenceRule(arrayOf(
            IdentifierTokenRule,
            object : Rule<Any> {
                override val explicitName = "branch"
                override fun startMatching(continueWith: MatchingContinuation<Any>): OngoingMatch {
                    val branches = listOf(
                        continueWith.resume(MatchingResult("A", emptySet())),
                        continueWith.resume(MatchingResult("B", emptySet())),
                        continueWith.resume(MatchingResult("C", emptySet())),
                    )
                    return object : OngoingMatch {
                        override fun step(token: Token): Boolean {
                            branches.forEach { it.step(token) }
                            return true
                        }
                    }

                }
            },
            IdentifierTokenRule,
        ), null)
            .flatten()
            .mapResult { it.remainingToList() }

        val completion = MultiCompletion()
        val matcher = rule.startMatching(completion)
        matcher.step(IdentifierToken("first"))
        matcher.step(IdentifierToken("second"))

        completion.results should haveSize(3)
        completion.results.forOne {
            it.item shouldBe listOf(
                IdentifierToken("first"),
                "A",
                IdentifierToken("second"),
            )
        }
        completion.results.forOne {
            it.item shouldBe listOf(
                IdentifierToken("first"),
                "B",
                IdentifierToken("second"),
            )
        }
        completion.results.forOne {
            it.item shouldBe listOf(
                IdentifierToken("first"),
                "C",
                IdentifierToken("second"),
            )
        }
    }
})