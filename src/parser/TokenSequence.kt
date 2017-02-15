package parser

import lexer.SourceLocation
import lexer.Token
import transact.Position
import transact.TransactionalSequence
import java.util.*

class TokenSequence(val tokens: List<Token>) : TransactionalSequence<Token, Position>(tokens)
{
    override var currentPosition: Position = Position(0)

    val currentSourceLocation: SourceLocation
        get() = tokens.getOrNull(currentPosition.sourceIndex)?.sourceLocation ?: throw IllegalStateException("Empty input: cannot read current token")

    override fun copyOfPosition(position: Position): Position = Position(position.sourceIndex)

    /** Returns the remaining tokens in a list */
    fun remainingToList(): List<Token> {
        return tokens.subList(currentPosition.sourceIndex, tokens.lastIndex)
    }
}

fun Sequence<Token>.toTransactional(): TokenSequence = TokenSequence(toList())