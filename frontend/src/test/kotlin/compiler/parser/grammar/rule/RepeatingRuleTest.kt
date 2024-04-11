package compiler.compiler.parser.grammar.rule

import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.FirstMatchCompletion
import compiler.reportings.ParsingMismatchReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.beEmpty
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
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
            val completion = FirstMatchCompletion<Any>()
            val matcher = grammar.startMatching(completion)
            matcher.step(KeywordToken(Keyword.EXPORT)) shouldBe true

            completion.result.reportings should beEmpty()
            completion.result.item shouldBe listOf(KeywordToken(Keyword.EXPORT))
        }

        "accepts one match" {
            val completion = FirstMatchCompletion<Any>()
            val matcher = grammar.startMatching(completion)
            matcher.step(KeywordToken(Keyword.IF)) shouldBe true
            matcher.step(KeywordToken(Keyword.EXPORT)) shouldBe true

            completion.result.reportings should beEmpty()
            completion.result.item shouldBe listOf(
                KeywordToken(Keyword.IF),
                KeywordToken(Keyword.EXPORT),
            )
        }

        "accepts four matches" {
            val completion = FirstMatchCompletion<Any>()
            val matcher = grammar.startMatching(completion)
            matcher.step(KeywordToken(Keyword.IF)) shouldBe true
            matcher.step(KeywordToken(Keyword.IF)) shouldBe true
            matcher.step(KeywordToken(Keyword.IF)) shouldBe true
            matcher.step(KeywordToken(Keyword.IF)) shouldBe true
            matcher.step(KeywordToken(Keyword.EXPORT)) shouldBe true

            completion.result.reportings should beEmpty()
            completion.result.item shouldBe listOf(
                KeywordToken(Keyword.IF),
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
            val completion = FirstMatchCompletion<Any>()
            val matcher = grammar.startMatching(completion)
            matcher.step(KeywordToken(Keyword.EXPORT)) shouldBe true

            completion.result.reportings should beEmpty()
            completion.result.item shouldBe listOf(KeywordToken(Keyword.EXPORT))
        }

        "accepts one match" {
            val completion = FirstMatchCompletion<Any>()
            val matcher = grammar.startMatching(completion)
            matcher.step(KeywordToken(Keyword.IF)) shouldBe true
            matcher.step(KeywordToken(Keyword.EXPORT)) shouldBe true

            completion.result.reportings should beEmpty()
            completion.result.item shouldBe listOf(
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
            val completion = FirstMatchCompletion<Any>()
            val matcher = grammar.startMatching(completion)
            matcher.step(KeywordToken(Keyword.IF)) shouldBe true
            matcher.step(KeywordToken(Keyword.IF)) shouldBe false

            completion.result.item shouldBe null
            completion.result.reportings should haveSize(1)
            completion.result.reportings.forOne {
                it.shouldBeInstanceOf<ParsingMismatchReporting>().also {
                    it.expectedAlternatives shouldBe listOf("keyword export")
                    it.actual shouldBe KeywordToken(Keyword.IF)
                }
            }
        }
    }
})