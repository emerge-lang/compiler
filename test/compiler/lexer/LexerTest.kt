/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.lexer

import io.kotlintest.matchers.*
import io.kotlintest.specs.FreeSpec

class LexerTest : FreeSpec() {init {

    val testSource = SimpleSourceDescriptor("test source code")

    "keywords" - {
        "default" {
            val result = Lexer("   module   ", testSource).remainingTokens().toList()

            result.size shouldBe 1
            result[0] should beInstanceOf(KeywordToken::class)
            (result[0] as KeywordToken).keyword shouldBe Keyword.MODULE
            (result[0] as KeywordToken).sourceText shouldEqual "module"
            (result[0] as KeywordToken).sourceLocation shouldEqual SourceLocation(testSource, 1, 4)
        }

        "should be case insensitive" {
            val result = Lexer(" MoDulE ", testSource).remainingTokens().toList()

            result.size should beGreaterThanOrEqualTo(1)
            result[0] should beInstanceOf(KeywordToken::class)
            (result[0] as KeywordToken).keyword shouldBe Keyword.MODULE
        }
    }

    "newlines are semantic" {
        val result = Lexer("  \n  \n  \n", testSource).remainingTokens().toList()

        result.size shouldEqual 3
        result[0] should beInstanceOf(OperatorToken::class)
        (result[0] as OperatorToken).operator shouldBe Operator.NEWLINE

        result[1] shouldEqual result[0]
        result[2] shouldEqual result[0]
    }

    "integers" - {
        "single digit" {
            val result = Lexer("7", testSource).remainingTokens().toList()

            result.size shouldEqual 1
            result[0] should beInstanceOf(NumericLiteralToken::class)
            (result[0] as NumericLiteralToken).stringContent shouldEqual "7"
        }

        "multiple digit" {
            val result = Lexer("21498743", testSource).remainingTokens().toList()

            result.size shouldEqual 1
            result[0] should beInstanceOf(NumericLiteralToken::class)
            (result[0] as NumericLiteralToken).stringContent shouldEqual "21498743"
        }
    }

    "decimals" - {
        "simple decimal" {
            val result = Lexer("312.1232", testSource).remainingTokens().toList()

            result.size shouldEqual 1
            result[0] should beInstanceOf(NumericLiteralToken::class)
            (result[0] as NumericLiteralToken).stringContent shouldEqual "312.1232"
        }

        "without leading digit it's not a decimal" {
            val result = Lexer(".25", testSource).remainingTokens().toList()

            result.size should beGreaterThan(1)
            result[0] shouldNot beInstanceOf(NumericLiteralToken::class)
        }

        "invocation on integer literal" {
            val result = Lexer("312.toLong()", testSource).remainingTokens().toList()

            result.size should beGreaterThan(3)
            result[0] should beInstanceOf(NumericLiteralToken::class)
            (result[0] as NumericLiteralToken).stringContent shouldEqual "312"

            result[1] should beInstanceOf(OperatorToken::class)
            (result[1] as OperatorToken).operator shouldBe Operator.DOT

            result[2] should beInstanceOf(IdentifierToken::class)
            (result[2] as IdentifierToken).value shouldEqual "toLong"
        }
    }

    "identifiers" - {
        "identifier stops at space" {
            val result = Lexer("foo bar", testSource).remainingTokens().toList()

            result.size shouldBe 2

            result[0] should beInstanceOf(IdentifierToken::class)
            (result[0] as IdentifierToken).value shouldEqual "foo"

            result[1] should beInstanceOf(IdentifierToken::class)
            (result[1] as IdentifierToken).value shouldEqual "bar"
        }

        "identifier stops at operator" {
            val result = Lexer("baz*", testSource).remainingTokens().toList()

            result.size shouldBe 2

            result[0] should beInstanceOf(IdentifierToken::class)
            (result[0] as IdentifierToken).value shouldEqual "baz"

            result[1] should beInstanceOf(OperatorToken::class)
            (result[1] as OperatorToken).operator shouldBe Operator.TIMES
        }

        "identifier stops at newline" {
            val result = Lexer("cat\n", testSource).remainingTokens().toList()

            result.size shouldBe 2

            result[0] should beInstanceOf(IdentifierToken::class)
            (result[0] as IdentifierToken).value shouldEqual "cat"

            result[1] should beInstanceOf(OperatorToken::class)
            (result[1] as OperatorToken).operator shouldBe Operator.NEWLINE
        }
    }

    "combo test with code" {
        val result = Lexer("""module foo
            fun foobar(val x: Int = 24) = return (142.12)?.toLong() == x
        """, testSource).remainingTokens().toList()

        result.size shouldBe 25

        result[0] should beInstanceOf(KeywordToken::class)
        (result[0] as KeywordToken).keyword shouldBe Keyword.MODULE

        result[1] should beInstanceOf(IdentifierToken::class)
        (result[1] as IdentifierToken).value shouldEqual "foo"

        result[2] should beInstanceOf(OperatorToken::class)
        (result[2] as OperatorToken).operator shouldBe Operator.NEWLINE

        result[3] should beInstanceOf(KeywordToken::class)
        (result[3] as KeywordToken).keyword shouldBe Keyword.FUNCTION

        result[4] should beInstanceOf(IdentifierToken::class)
        (result[4] as IdentifierToken).value shouldEqual "foobar"

        result[5] should beInstanceOf(OperatorToken::class)
        (result[5] as OperatorToken).operator shouldBe Operator.PARANT_OPEN

        result[6] should beInstanceOf(KeywordToken::class)
        (result[6] as KeywordToken).keyword shouldBe Keyword.VAL

        result[7] should beInstanceOf(IdentifierToken::class)
        (result[7] as IdentifierToken).value shouldEqual "x"

        result[8] should beInstanceOf(OperatorToken::class)
        (result[8] as OperatorToken).operator shouldBe Operator.COLON

        result[9] should beInstanceOf(IdentifierToken::class)
        (result[9] as IdentifierToken).value shouldEqual "Int"

        result[10] should beInstanceOf(OperatorToken::class)
        (result[10] as OperatorToken).operator shouldBe Operator.ASSIGNMENT

        result[11] should beInstanceOf(NumericLiteralToken::class)
        (result[11] as NumericLiteralToken).stringContent shouldEqual "24"

        result[12] should beInstanceOf(OperatorToken::class)
        (result[12] as OperatorToken).operator shouldBe Operator.PARANT_CLOSE

        result[13] should beInstanceOf(OperatorToken::class)
        (result[13] as OperatorToken).operator shouldBe Operator.ASSIGNMENT

        result[14] should beInstanceOf(KeywordToken::class)
        (result[14] as KeywordToken).keyword shouldBe Keyword.RETURN

        result[15] should beInstanceOf(OperatorToken::class)
        (result[15] as OperatorToken).operator shouldBe Operator.PARANT_OPEN

        result[16] should beInstanceOf(NumericLiteralToken::class)
        (result[16] as NumericLiteralToken).stringContent shouldEqual "142.12"

        result[17] should beInstanceOf(OperatorToken::class)
        (result[17] as OperatorToken).operator shouldBe Operator.PARANT_CLOSE

        result[18] should beInstanceOf(OperatorToken::class)
        (result[18] as OperatorToken).operator shouldBe Operator.SAFEDOT

        result[19] should beInstanceOf(IdentifierToken::class)
        (result[19] as IdentifierToken).value shouldEqual "toLong"

        result[20] should beInstanceOf(OperatorToken::class)
        (result[20] as OperatorToken).operator shouldBe Operator.PARANT_OPEN

        result[21] should beInstanceOf(OperatorToken::class)
        (result[21] as OperatorToken).operator shouldBe Operator.PARANT_CLOSE

        result[22] should beInstanceOf(OperatorToken::class)
        (result[22] as OperatorToken).operator shouldBe Operator.EQUALS

        result[23] should beInstanceOf(IdentifierToken::class)
        (result[23] as IdentifierToken).value shouldEqual "x"

        result[24] should beInstanceOf(OperatorToken::class)
        (result[24] as OperatorToken).operator shouldBe Operator.NEWLINE
    }
}}