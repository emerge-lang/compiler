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

/**
 * @param addTrailingNewline if true, this function will make sure there is a trailing newline token in
 * the result and that the very last token is an [EndOfInputToken].
 */
fun lex(sourceFile: SourceFile, addTrailingNewline: Boolean = true): Array<Token> {
    val iterator = PositionTrackingCodePointTransactionalSequence(sourceFile.content.codePoints().toArray())
    val tokens = ArrayList<Token>()

    tokenLoop@ while (iterator.hasNext) {
        iterator.skipWhitespace()
        if (!iterator.hasNext) {
            break@tokenLoop
        }

        val operatorToken = iterator.tryMatchOperator(sourceFile)
        if (operatorToken != null) {
            if (operatorToken.operator == Operator.COMMENT) {
                iterator.skipRestOfLine()
                continue@tokenLoop
            }

            tokens.add(operatorToken)

            when (operatorToken.operator) {
                Operator.STRING_DELIMITER -> {
                    val (content, contentLocation) = iterator.collectStringContent(sourceFile)
                    tokens.add(StringLiteralContentToken(contentLocation, content))
                    if (!iterator.hasNext) {
                        break@tokenLoop
                    }
                    val endDelimiter = iterator.tryMatchOperator(sourceFile)
                    check(endDelimiter != null && endDelimiter.operator == Operator.STRING_DELIMITER)
                    tokens.add(endDelimiter)
                }
                Operator.IDENTIFIER_DELIMITER -> {
                    val (content, contentLocation) = iterator.collectDelimitedIdentifierContent(sourceFile)
                    tokens.add(DelimitedIdentifierContentToken(contentLocation, content))
                    if (!iterator.hasNext) {
                        break@tokenLoop
                    }
                    val endDelimiter = iterator.tryMatchOperator(sourceFile)
                    check(endDelimiter != null && endDelimiter.operator == Operator.IDENTIFIER_DELIMITER)
                    tokens.add(endDelimiter)
                }
                else -> {}
            }

            continue@tokenLoop
        }

        val numericLiteralToken = iterator.tryMatchNumericLiteral(sourceFile)
        if (numericLiteralToken != null) {
            tokens.add(numericLiteralToken)
            continue@tokenLoop
        }

        // IDENTIFIER or KEYWORD
        val text = iterator.collectUntilOperatorOrWhitespace(sourceFile)

        // check against keywords
        val keyword = Keyword.entries.firstOrNull { it.text.equals(text.first, true) }

        if (keyword != null) {
            tokens.add(KeywordToken(keyword, text.first, text.second))
            continue@tokenLoop
        }

        tokens.add(IdentifierToken(text.first, text.second))
    }

    if (addTrailingNewline) {
        // this is not needed for lexing or parsing in general; but the grammar for the emerge language wants
        // a newline at the end of the file, always
        var lastToken = tokens.lastOrNull()
        if (lastToken !is OperatorToken || lastToken.operator != Operator.NEWLINE) {
            tokens.add(
                OperatorToken(
                    Operator.NEWLINE,
                    lastToken?.span?.copy(
                        fromLineNumber = lastToken.span.toLineNumber,
                        fromColumnNumber = lastToken.span.toColumnNumber + 1u,
                        toColumnNumber = lastToken.span.toColumnNumber + 1u,
                    ) ?: Span(sourceFile, 1u, 1u, 1u, 1u)
                )
            )
        }

        lastToken = tokens.last()
    }

    // this is also not strictly needed for lexing, but enables parsing
    tokens.add(EndOfInputToken(tokens.last().span))

    return tokens.toTypedArray()
}

private fun PositionTrackingCodePointTransactionalSequence.skipWhitespace() {
    while (peek()?.isWhitespace == true)
    {
        nextOrThrow()
    }
}

private fun PositionTrackingCodePointTransactionalSequence.skipRestOfLine() {
    while (hasNext) {
        val next = peek()!!
        if (next.isLinefeed) {
            break
        }
        nextOrThrow()
    }
}

private fun PositionTrackingCodePointTransactionalSequence.nextCodePointsAsString(sourceFile: SourceFile, n: Int): Pair<String, Span>? {
    check(n > 0)
    if (nCodePointsRemaining < n) {
        return null
    }

    val buf = StringBuffer(n)
    buf.appendCodePoint(nextOrThrow().value)
    val start = currentPosition
    repeat(n - 1) {
        buf.appendCodePoint(nextOrThrow().value)
    }

    return Pair(buf.toString(), Span(sourceFile, start, currentPosition))
}

private fun PositionTrackingCodePointTransactionalSequence.tryMatchOperator(sourceFile: SourceFile, doCommit: Boolean = true): OperatorToken? {
    for (operator in Operator.valuesSortedForLexing) {
        mark()

        val nextText = nextCodePointsAsString(sourceFile, operator.text.length)
        if (nextText != null && nextText.first == operator.text) {
            if (doCommit) commit() else rollback()
            return OperatorToken(operator, nextText.second)
        }

        rollback()
    }

    return null
}

private fun PositionTrackingCodePointTransactionalSequence.collectUntilOperatorOrWhitespace(sourceFile: SourceFile): Pair<String, Span> {
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

    return Pair(buf.toString(), Span(sourceFile, start ?: currentPosition, currentPosition))
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
                firstIntegerStringLocation .. fractionalStringLocation,
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

private fun PositionTrackingCodePointTransactionalSequence.collectStringContent(sourceFile: SourceFile): Pair<String, Span> {
    val data = StringBuilder()
    var start: SourceSpot? = null
    while (true) {
        val peeked = peek() ?: break

        if (peeked == STRING_ESCAPE_CHAR) {
            nextOrThrow()
            val escapeStart = currentPosition
            val next = try {
                nextOrThrow() // consume
            } catch (ex: NoSuchElementException) {
                throw IllegalEscapeSequenceException(Span(sourceFile, escapeStart, currentPosition), "Unexpected EOF in escape sequence", ex)
            }

            val actualChar = ESCAPE_SEQUENCES[next]
                ?: throw IllegalEscapeSequenceException(Span(sourceFile, escapeStart, currentPosition), "Illegal escape sequence")

            data.appendCodePoint(actualChar.value)
            continue
        }

        if (peeked == STRING_DELIMITER) {
            // ending delimiter will be processed by the caller
            break
        }

        nextOrThrow() // consume
        start = start ?: currentPosition
        data.appendCodePoint(peeked.value)
    }

    return Pair(data.toString(), Span(sourceFile, start ?: currentPosition, currentPosition))
}

private fun PositionTrackingCodePointTransactionalSequence.collectDelimitedIdentifierContent(sourceFile: SourceFile): Pair<String, Span> {
    val data = StringBuilder()
    var start: SourceSpot? = null
    while (true) {
        val peeked = peek() ?: break

        if (peeked == IDENTIFIER_DELIMITER) {
            // ending delimiter will be processed by the caller
            break
        }

        nextOrThrow()
        start = start ?: currentPosition
        data.appendCodePoint(peeked.value)
    }

    return Pair(data.toString(), Span(sourceFile, start ?: currentPosition, currentPosition))
}

private val ESCAPE_SEQUENCES: Map<CodePoint, CodePoint> = mapOf<Char, Char>(
    'n' to '\n',
    't' to '\t',
    'r' to '\r',
).entries.associate {
    CodePoint(it.key.code) to CodePoint(it.value.code)
}