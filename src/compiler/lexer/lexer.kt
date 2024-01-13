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

import compiler.parser.TokenSequence

fun SourceFile.lex(): TokenSequence {
    val iterator = PositionTrackingCodePointTransactionalSequence(this@lex.content.codePoints().toArray())
    val initialSourceLocation = SourceLocation(this@lex, iterator.currentPosition, iterator.currentPosition)

    val generator = sequence {
        tokenLoop@while (iterator.hasNext) {
            iterator.skipWhitespace()
            if (!iterator.hasNext) {
                return@sequence
            }

            val operator = iterator.tryMatchOperator(this@lex)
            if (operator != null) {
                yield(operator)
                continue@tokenLoop
            }

            val numeric = iterator.tryMatchNumericLiteral(this@lex)
            if (numeric != null) {
                yield(numeric)
                continue@tokenLoop
            }

            // IDENTIFIER or KEYWORD
            val text = iterator.collectUntilOperatorOrWhitespace(this@lex)

            // check against keywords
            val keyword = Keyword.values().firstOrNull { it.text.equals(text.first, true) }

            if (keyword != null) {
                yield(KeywordToken(keyword, text.first, text.second))
                continue@tokenLoop
            }

            yield(IdentifierToken(text.first, text.second))
        }
    }

    return TokenSequence(generator.toList(), initialSourceLocation)
}

private fun PositionTrackingCodePointTransactionalSequence.skipWhitespace() {
    while (peek()?.isWhitespace == true)
    {
        nextOrThrow()
    }
}

// TODO: rename to nextCodePointsAsString
private fun PositionTrackingCodePointTransactionalSequence.nextChars(n: Int): String? {
    if (nCodePointsRemaining < n) {
        return null
    }

    val buf = StringBuffer(n)
    repeat(n) {
        buf.appendCodePoint(nextOrThrow().value)
    }

    return buf.toString()
}

private fun PositionTrackingCodePointTransactionalSequence.tryMatchOperator(sourceFile: SourceFile, doCommit: Boolean = true): OperatorToken? {
    for (operator in Operator.valuesSortedForLexing) {
        mark()

        val start = currentPosition
        val nextText = nextChars(operator.text.length)
        if (nextText != null && nextText == operator.text) {
            if (doCommit) commit() else rollback()
            return OperatorToken(operator, SourceLocation(sourceFile, start, currentPosition))
        }

        rollback()
    }

    return null
}

private fun PositionTrackingCodePointTransactionalSequence.collectUntilOperatorOrWhitespace(sourceFile: SourceFile): Pair<String, SourceLocation> {
    val buf = StringBuilder()
    var start: SourceSpot? = null

    while (hasNext) {
        val operator = tryMatchOperator(sourceFile, false)
        if (operator != null) break

        if (peek()!!.isWhitespace) {
            break
        }

        buf.appendCodePoint(nextOrThrow().value)
        start = start ?: currentPosition
    }

    return Pair(buf.toString(), SourceLocation(sourceFile, start ?: currentPosition, currentPosition))
}

private fun PositionTrackingCodePointTransactionalSequence.tryMatchNumericLiteral(sourceFile: SourceFile): NumericLiteralToken? {
    if (peek()?.isDigit == false) {
        return null
    }
    // NUMERIC_LITERAL
    val (firstIntegerString, firstIntegerStringLocation) = collectUntilOperatorOrWhitespace(sourceFile)
    mark()
    if (peek() == DECIMAL_SEPARATOR) {
        // skip the dot
        nextOrThrow()

        if (peek()?.isDigit != false) {
            // <DIGIT, ...> <DOT> <DIGIT, ...> => Floating point literal
            commit()
            // floating point literal
            val floatBuilder = StringBuilder(firstIntegerString)
            floatBuilder.appendCodePoint(DECIMAL_SEPARATOR.value)
            val (fractionalString, fractionalStringLocation) = collectUntilOperatorOrWhitespace(sourceFile)
            floatBuilder.append(fractionalString)

            // return numericStr later
            return NumericLiteralToken(
                SourceLocation(
                    sourceFile,
                    firstIntegerStringLocation.fromSourceLineNumber,
                    firstIntegerStringLocation.toColumnNumber,
                    fractionalStringLocation.toSourceLineNumber,
                    fractionalStringLocation.toColumnNumber,
                ),
                floatBuilder.toString(),
            )
        }
        else {
            // <DIGIT, ...> <DOT> <!DIGIT, ...> => member access on numeric literal
            // rollback before the ., so that the next invocation yields an OperatorToken
            rollback()

            // return numericStr later
        }
    }

    return NumericLiteralToken(firstIntegerStringLocation, firstIntegerString)
}