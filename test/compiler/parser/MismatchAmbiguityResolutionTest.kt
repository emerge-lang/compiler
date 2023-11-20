package compiler.parser

import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.negative.lexCode
import compiler.negative.shouldReport
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence
import compiler.reportings.ParsingErrorReporting
import compiler.reportings.TokenMismatchReporting
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.beEmpty
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe
import io.kotest.matchers.types.shouldBeInstanceOf

class MismatchAmbiguityResolutionTest : FreeSpec({
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
        result.reportings.shouldReport<ParsingErrorReporting>()
    }

    "mismatch after disambiguifying token in first branch" {
        val tokens = lexCode("external operator nothrow struct", addModuleDeclaration = false)
        val result = grammar.tryMatch(Unit, tokens)

        result.item shouldBe null
        result.isAmbiguous shouldBe false
        result.reportings.shouldReport<TokenMismatchReporting> {
            it.expected shouldBe KeywordToken(Keyword.FUNCTION)
            it.actual shouldBe KeywordToken(Keyword.STRUCT_DEFINITION)
        }
    }

    "mismatch after disambiguifying token in second branch" {
        val tokens = lexCode("external operator readonly struct", addModuleDeclaration = false)
        val result = grammar.tryMatch(Unit, tokens)

        result.item shouldBe null
        result.isAmbiguous shouldBe false
        result.reportings.shouldReport<TokenMismatchReporting> {
            it.expected shouldBe KeywordToken(Keyword.VAL)
            it.actual shouldBe KeywordToken(Keyword.STRUCT_DEFINITION)
        }
    }

    "fail before ambiguity in outer sequence" {
        val tokens = lexCode("foo", addModuleDeclaration = false)
        val result = grammar.tryMatch(Unit, tokens)

        result.reportings.shouldReport<TokenMismatchReporting> {
            it.expected shouldBe KeywordToken(Keyword.EXTERNAL)
            it.actual shouldBe IdentifierToken("foo")
        }
    }

    "around repeating" {
        TODO("how to handle ambiguity in results in RepeatingRule?")
        // TODO: how does the minimal sequence behave around repeating {} and repeatingAtLeastOnce {} ?
        // i suspect this is the cause of the current parsing problems, solving it will get us a major step closer
        // to FINALLY being able to close the parser chapter...
    }
})