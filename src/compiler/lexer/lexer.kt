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
        for (operator in Operator.values())
        {
            sourceTxSequence.mark()

            val nextText = nextChars(operator.text.length)
            if (nextText != null && nextText == operator.text) {
                sourceTxSequence.commit()
                return OperatorToken(operator, currentSL)
            }

            sourceTxSequence.rollback()
        }

        if (!hasNext) return null

        // remaining possibilities: NUMERIC_LITERAL, KEYWORD, IDENTIFIER
        val text = collectWhile(Not(IsOperatorChar or IsWhitespace))!!

        // check against keywords
        val keyword = Keyword.values()
                .firstOrNull { it.text.equals(text, true) }

        if (keyword != null) return KeywordToken(keyword, currentSL)

        if (IsIntegerLiteral(text))
        {
            return IntegerLiteralToken(currentSL, text)
        }
        else if (IsFloatingPointLiteral(text))
        {
            return FloatingPointLiteralToken(currentSL, text)
        }
        else
        {
            return IdentifierToken(text, currentSL)
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