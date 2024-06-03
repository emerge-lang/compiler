package compiler.compiler.parser

import compiler.compiler.MockEOIToken
import compiler.compiler.negative.lexCode
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.grammar.dsl.GrammarReceiver
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.flatten
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.MatchingResult
import compiler.parser.grammar.rule.matchAgainst
import io.kotest.core.spec.style.FreeSpec
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
            endOfInput()
        }.flatten().mapResult { it.remainingToList() }

        "match first path" {
            val tokens = lexCode("intrinsic operator nothrow fn", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
            (result.item)[0] shouldBe KeywordToken(Keyword.INTRINSIC)
            (result.item)[1] shouldBe KeywordToken(Keyword.OPERATOR)
            (result.item)[2] shouldBe KeywordToken(Keyword.NOTHROW)
            (result.item)[3] shouldBe KeywordToken(Keyword.FUNCTION)
        }

        "match second path with backtracing" {
            val tokens = lexCode("intrinsic operator read var", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
            (result.item)[0] shouldBe KeywordToken(Keyword.INTRINSIC)
            (result.item)[1] shouldBe KeywordToken(Keyword.OPERATOR)
            (result.item)[2] shouldBe KeywordToken(Keyword.READONLY)
            (result.item)[3] shouldBe KeywordToken(Keyword.VAR)
        }

        "mismatch on ambiguous token" {
            val tokens = lexCode("intrinsic operator pure fn", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Error>()
        }

        "mismatch after disambiguifying token in first branch" {
            val tokens = lexCode("intrinsic operator nothrow class", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Error>()
            result.reporting.expectedAlternatives shouldBe listOf("keyword fn")
            result.reporting.actual shouldBe KeywordToken(Keyword.CLASS_DEFINITION)
        }

        "mismatch after disambiguifying token in second branch" {
            val tokens = lexCode("intrinsic operator read class", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Error>()
            result.reporting.expectedAlternatives shouldBe listOf("keyword var")
            result.reporting.actual shouldBe KeywordToken(Keyword.CLASS_DEFINITION)
        }

        "fail before ambiguity in outer sequence" {
            val tokens = lexCode("class", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Error>()
            result.reporting.expectedAlternatives shouldBe listOf("keyword intrinsic")
            result.reporting.actual shouldBe KeywordToken(Keyword.CLASS_DEFINITION)
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
            endOfInput()
        }
            .flatten()
            .mapResult { it.remainingToList() }

        "must not affect other ambiguous branches" {
            val tokens = lexCode("b e", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
            result.item shouldBe listOf(
                IdentifierToken("b"),
                IdentifierToken("e"),
            )
        }

        "mismatch in unambiguous branch should prevent backtracking" {
            val tokens = lexCode("c a", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Error>()
            result.reporting.expectedAlternatives shouldBe listOf("identifier d")
            result.reporting.actual shouldBe IdentifierToken("a")
        }
    }

    "optional" - {
        "simpler" {
            val grammar = sequence {
                optional {
                    eitherOf {
                        identifier("preA")
                        identifier("preB")
                    }
                }
                identifier("a")
                endOfInput()
            }
                .flatten()
                .mapResult { it.remainingToList() }

            val tokens = lexCode("preA a", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
            result.item shouldBe listOf(
                IdentifierToken("preA"),
                IdentifierToken("a"),
            )
        }

        "should recognize ambiguity introduced by optional tokens" {
            val grammar = sequence {
                eitherOf {
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
                endOfInput()
            }
                .flatten()
                .mapResult { it.remainingToList() }

            val tokens = lexCode("preA b", addPackageDeclaration = false)
            val result = matchAgainst(tokens, grammar)

            result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
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

        val result = matchAgainst(arrayOf(
            IdentifierToken("identifier"),
            MockEOIToken,
        ), expr)

        result.shouldBeInstanceOf<MatchingResult.Success<List<Any>>>()
        result.item shouldBe listOf(IdentifierToken("identifier"))
    }
})

private fun GrammarReceiver.identifier(value: String) {
    tokenEqualTo(IdentifierToken(value))
}