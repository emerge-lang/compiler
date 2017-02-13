package lexer

import java.util.*

class Lexer(private val input: List<Char>, private val sourceDescriptor: SourceDescriptor)
{
    /**
     * This class works by performing "transactions" on the input list. The current location is stored in
     * currentLocation; whenever an operation with unknown outcome is attempted, invoke mark(). That puts the
     * current location onto a stack. If the operation succeeds, invoke commit(). That will pop that location
     * off the stack again. If it fails, invoke resume(). That will reset the state to where it was when mark()
     * was last invoked.
     */

    /**
     * @return The next token from the input or `null` if there are no more tokens.
     */
    @Synchronized
    fun next(): Token?
    {
        skipWhitespace()

        if (!hasNextChar()) return null

        // try to match an operator
        for (operator in Operator.values())
        {
            val opToken = transact {
                val nextText = nextChars(operator.text.length) ?: failTx()
                if (nextText == operator.text) {
                    return@transact OperatorToken(currentSL, operator)
                }
                failTx()
            }

            if (opToken != null) return opToken
        }

        if (!hasNextChar()) return null

        // remaining possibilities: NUMERIC_LITERAL, KEYWORD, IDENTIFIER
        val text = collectWhile(Not(IsOperatorChar or IsWhitespace))!!

        // check against keywords
        val keyword = Keyword.values()
                .firstOrNull { it.text.equals(text, true) }

        if (keyword != null) return KeywordToken(currentSL, keyword)

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
            return IdentifierToken(currentSL, text)
        }
    }

    /** current location **/
    private var currentLocation: LocationRef = LocationRef(1, 1, 0)

    /**
     * Returns the next character from the input and advances the input state; changes source line and column if
     * necessary. **Invoke [mark] first if you are not 100% certain that you will use the return value for the current
     * token.**
     */
    private fun nextChar(): Char?
    {
        if (input.lastIndex < currentLocation.inputIndex)
        {
            return null
        }

        val char = input[currentLocation.inputIndex]

        if (currentLocation.inputIndex > 0) {
            var previousChar = input[currentLocation.inputIndex - 1]
            if (previousChar == '\n')
            {
                currentLocation.sourceLine++
                currentLocation.sourceColumn = 1
            }
            else
            {
                currentLocation.sourceColumn++
            }
        }

        currentLocation.inputIndex++

        return char
    }

    /**
     * @return Whether an invocation of [nextChar] would yield a result.
     */
    private fun hasNextChar(): Boolean {
        return input.lastIndex >= currentLocation.inputIndex
    }

    /**
     * Returns the next [n] chars from the input as a string. Basically invokes [nextChar] [n] times and concatenates
     * the results.
     * @return The next [n] chars from the input or `null` if there are not enough chars left in the input.
     */
    private fun nextChars(n: Int): String?
    {
        if (currentLocation.inputIndex + n - 1 > input.lastIndex)
        {
            return null
        }

        val buf = StringBuilder(n)
        for (i in 0..n - 1) {
            buf.append(nextChar()!!)
        }
        return buf.toString()
    }

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
            mark()
            char = nextChar()
            if (char != null && pred(char)) {
                buf.append(char)
                commit()
            }
            else {
                resume()
                break
            }
        }

        return buf.toString()
    }

    /** Skips whitespace according to [IsWhitespace]. Equals `collectWhile(IsWhitespace)` */
    private fun skipWhitespace() {
        collectWhile(IsWhitespace)
    }

    // here follows the transaction management code
    private var markedPositions: Stack<LocationRef> = Stack()

    /**
     * Remembers the current location in the source. Use in conjunction with [commit] and [resume].
     */
    private fun mark()
    {
        markedPositions.push(currentLocation.copy())
    }

    /**
     * Discards the last remembered location using [mark]. Invoke this method once you are sure that the characters
     * you have consumed so fare will be returned in a token.
     * @param nSteps The number of [mark] steps to erase.
     */
    private fun commit(nSteps: Int = 1)
    {
        for (i in 0..nSteps - 1) markedPositions.pop()
    }

    /**
     * Resets the current source location to the last remembered location using [mark]. Use this if, after consuming
     * some characters, it has turned out that they cannot be evaluated just yet.
     * @param nSteps The number of [mark] steps to resume
     */
    private fun resume(nSteps: Int = 1) {
        for (i in 0..nSteps - 1) currentLocation = markedPositions.pop()
    }

    /**
     * Runs the given function within a "transaction" on the lexer state. If the function throws an exception,
     * the state is reset and the exception is passed on. If the function returns gracefully, the result is passed on.
     * @return The result of the given function or `null` if the function throws a [FailLexerTransactionException] (see [failTx]).
     */
    private fun <T> transact(txCode: Lexer.() -> T): T?
    {
        mark()
        try
        {
            val retVal = this.txCode()
            commit()
            return retVal
        }
        catch (ex: Throwable)
        {
            resume()
            if (ex is FailLexerTransactionException)
            {
                return null
            }
            else
            {
                throw ex
            }
        }
    }

    /**
     * @throws FailLexerTransactionException Does nothing else; for use within [transact]
     */
    private fun failTx(): Nothing = throw FailLexerTransactionException()

    private val currentSL: SourceLocation
        get() = sourceDescriptor.toLocation(currentLocation.sourceLine, currentLocation.sourceColumn)

    private companion object {
        class FailLexerTransactionException : Exception()

        data class LocationRef(
            var sourceLine: Int,
            var sourceColumn: Int,
            var inputIndex: Int
        )
    }
}

/**
 * Lexes the given code. The resulting tokens use the given [SourceDescriptor] to refer to their location in the
 * source.
 */
public fun lex(code: String, sD: SourceDescriptor): Sequence<Token> {
    val lexer = Lexer(code.toCharArray().asList(), sD)

    return lexer.remainingTokens()
}

/**
 * Lexes the given code.
 */
public fun lex(source: SourceContentAwareSourceDescriptor): Sequence<Token> {
    val code = source.sourceLines.joinToString("\n")

    val lexer = Lexer(code.toCharArray().asList(), source)

    return lexer.remainingTokens()
}

/**
 * Collects all the remaining tokens of the lexer into a collection and returns it.
 */
public fun Lexer.remainingTokens(): Sequence<Token> {
    val tokens = LinkedList<Token>()

    while (true)
    {
        val token = next()
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