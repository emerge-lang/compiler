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

import compiler.transact.SourceFileReader
import compiler.transact.TransactionalSequence
import java.util.*

class Lexer(code: String, private val sourceDescriptor: SourceDescriptor)
{
    private val sourceTxSequence = SourceFileReader(code)

    /**
     * @return The nextToken token from the input or `null` if there are no more tokens.
     */
    @Synchronized
    fun nextToken(): Token?
    {
        skipWhitespace()

        if (!hasNext) return null

        // try to match an operator
        val operator = tryMatchOperator()
        if (operator != null) return operator

        if (!hasNext) return null

        if (sourceTxSequence.peek()!!.isDigit()) {
            // NUMERIC_LITERAL
            var numericStr = collectUntilOperatorOrWhitespace()
            sourceTxSequence.mark()
            if (sourceTxSequence.peek() == DECIMAL_SEPARATOR) {
                // skip the dot
                sourceTxSequence.next()

                if (sourceTxSequence.peek()?.isDigit() ?: true) {
                    // <DIGIT, ...> <DOT> <DIGIT, ...> => Floating point literal
                    sourceTxSequence.commit()
                    // floating point literal
                    numericStr += DECIMAL_SEPARATOR + collectUntilOperatorOrWhitespace()

                    // return numericStr later
                }
                else {
                    // <DIGIT, ...> <DOT> <!DIGIT, ...> => member access on numeric literal
                    // rollback before the ., so that the next invocation yields an OperatorToken
                    sourceTxSequence.rollback()

                    // return numericStr later
                }
            }

            return NumericLiteralToken(currentSL.minusChars(numericStr.length), numericStr)
        }
        else {
            // IDENTIFIER or KEYWORD
            val text = collectUntilOperatorOrWhitespace()

            // check against keywords
            val keyword = Keyword.values().firstOrNull { it.text.equals(text, true) }

            if (keyword != null) return KeywordToken(keyword, text, currentSL.minusChars(text.length))

            return IdentifierToken(text, currentSL.minusChars(text.length))
        }
    }

    private val hasNext: Boolean
        get() = sourceTxSequence.hasNext()

    private fun nextChar(): Char? = sourceTxSequence.next()

    private fun nextChars(n: Int): String? = sourceTxSequence.next(n)

    private fun <T> transact(txCode: TransactionalSequence<Char, SourceFileReader.SourceLocation>.TransactionReceiver.() -> T): T? = sourceTxSequence.transact(txCode)

    /**
     * Collects chars from the input as long as they fulfill [pred]. If a character is encountered that does not
     * fulfill the predicate, the collecting is stopped and the characters collected so far are returned. The character
     * causing the break can then be obtained using [nextChar].
     */
    private fun collectWhile(pred: (Char) -> Boolean): String?
    {
        var buf = StringBuilder()

        var char: Char?
        while (true)
        {
            sourceTxSequence.mark()
            char = sourceTxSequence.next()
            if (char != null && pred(char)) {
                buf.append(char)
                sourceTxSequence.commit()
            }
            else {
                sourceTxSequence.rollback()
                break
            }
        }

        return buf.toString()
    }

    private fun collectUntilOperatorOrWhitespace(): String {
        var buf = StringBuilder()

        while (sourceTxSequence.hasNext()) {
            val operator = tryMatchOperator(false)
            if (operator != null) break

            if (IsWhitespace(sourceTxSequence.peek()!!)) break
            buf.append(sourceTxSequence.next()!!)
        }

        return buf.toString()
    }

    private fun tryMatchOperator(doCommit: Boolean = true): OperatorToken? {
        for (operator in Operator.valuesSortedForLexing)
        {
            sourceTxSequence.mark()

            val nextText = nextChars(operator.text.length)
            if (nextText != null && nextText == operator.text) {
                if (doCommit) sourceTxSequence.commit() else sourceTxSequence.rollback()
                return OperatorToken(operator, currentSL.minusChars(nextText.length))
            }

            sourceTxSequence.rollback()
        }

        return null
    }

    /** Skips whitespace according to [IsWhitespace]. Equals `collectWhile(IsWhitespace)` */
    private fun skipWhitespace() {
        collectWhile(IsWhitespace)
    }

    private val currentSL: SourceLocation
        get() = sourceDescriptor.toLocation(
                sourceTxSequence.currentPosition.lineNumber,
                sourceTxSequence.currentPosition.columnNumber
        )
}

/**
 * Lexes the given code. The resulting tokens use the given [SourceDescriptor] to refer to their location in the
 * source.
 */
public fun lex(code: String, sD: SourceDescriptor): Sequence<Token> {
    val lexer = Lexer(code, sD)

    return lexer.remainingTokens()
}

/**
 * Lexes the given code.
 */
public fun lex(source: SourceContentAwareSourceDescriptor): Sequence<Token> {
    val code = source.sourceLines.joinToString("\n")

    val lexer = Lexer(code, source)

    return lexer.remainingTokens()
}

/**
 * Collects all the remaining tokens of the compiler.lexer into a collection and returns it.
 */
public fun Lexer.remainingTokens(): Sequence<Token> {
    val tokens = LinkedList<Token>()

    while (true)
    {
        val token = nextToken()
        if (token != null)
        {
            tokens.add(token)
        }
        else
        {
            break
        }
    }

    return tokens.asSequence()
}