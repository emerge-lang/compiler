package parser

import lexer.SourceLocation
import lexer.Token
import transact.Position
import transact.TransactionalSequence

class TokenSequence(val tokens: List<Token>) : TransactionalSequence<Token, Position>(tokens)
{
    override var currentPosition: Position = Position(0)

    val currentSourceLocation: SourceLocation
        get() = tokens.getOrNull(currentPosition.sourceIndex)?.sourceLocation ?: throw IllegalStateException("Empty input: cannot read current token")

    override fun copyOfPosition(position: Position): Position = Position(position.sourceIndex)
}