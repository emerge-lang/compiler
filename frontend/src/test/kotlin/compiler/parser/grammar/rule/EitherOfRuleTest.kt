package compiler.compiler.parser.grammar.rule

import compiler.lexer.EndOfInputToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.FirstMatchCompletion
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forAll
import io.kotest.matchers.collections.beEmpty
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.mockk.mockk

class EitherOfRuleTest : FreeSpec({
    "minimal" - {
        "first" {
            val grammar = eitherOf {
                keyword(Keyword.INTRINSIC)
                keyword(Keyword.OPERATOR)
            }
            val completion = FirstMatchCompletion<Any>()
            val matcher = grammar.startMatching(completion)
            matcher.step(KeywordToken(Keyword.INTRINSIC)) shouldBe true

            completion.result.reportings should beEmpty()
            completion.result.item shouldBe KeywordToken(Keyword.INTRINSIC)
        }

        "second" {
            val grammar = eitherOf {
                keyword(Keyword.INTRINSIC)
                keyword(Keyword.OPERATOR)
            }
            val completion = FirstMatchCompletion<Any>()
            val matcher = grammar.startMatching(completion)
            matcher.step(KeywordToken(Keyword.OPERATOR)) shouldBe true

            completion.result.reportings should beEmpty()
            completion.result.item shouldBe KeywordToken(Keyword.OPERATOR)
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

        val completion = FirstMatchCompletion<Any>()
        val match = grammar.startMatching(completion)
        match.step(KeywordToken(Keyword.IF)) shouldBe true
        match.step(KeywordToken(Keyword.ELSE)) shouldBe true

        completion.result.item shouldBe listOf(
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

        val completion = FirstMatchCompletion<Any>()
        val match = grammar.startMatching(completion)
        match.step(KeywordToken(Keyword.IF)) shouldBe true
        match.step(KeywordToken(Keyword.ELSE)) shouldBe true

        completion.result.item shouldBe listOf(
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

        val completion = FirstMatchCompletion<Any>()
        val match = grammar.startMatching(completion)
        match.step(KeywordToken(Keyword.IF))
        match.step(KeywordToken(Keyword.EXPORT))
        match.step(KeywordToken(Keyword.CLASS_DEFINITION))

        completion.result.item shouldBe listOf(
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

        val completion = FirstMatchCompletion<Any>()
        val match = grammar.startMatching(completion)
        match.step(KeywordToken(Keyword.IF)) shouldBe true
        match.step(KeywordToken(Keyword.ELSE)) shouldBe true
        match.step(KeywordToken(Keyword.CLASS_DEFINITION)) shouldBe true
        match.step(EndOfInputToken(mockk())) shouldBe true

        completion.result.item shouldBe listOf(
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

        val completion = MultiCompletion()
        val matcher = grammar.startMatching(completion)
        matcher.step(KeywordToken(Keyword.IF)) shouldBe true

        completion.results should haveSize(2)
        completion.results.forAll {
            it.item shouldBe KeywordToken(Keyword.IF)
            it.reportings should beEmpty()
        }
    }
})