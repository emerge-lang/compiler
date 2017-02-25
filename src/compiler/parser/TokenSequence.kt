package compiler.parser

import compiler.lexer.SourceLocation
import compiler.lexer.Token
import compiler.transact.Position
import compiler.transact.TransactionalSequence

class TokenSequence(val tokens: List<Token>) : TransactionalSequence<Token, Position>(tokens)
{
    override var currentPosition: Position = Position(0)

    val currentSourceLocation: SourceLocation
        get() = tokens.getOrNull(currentPosition.sourceIndex)?.sourceLocation ?: throw IllegalStateException("Empty input: cannot read current token")

    override fun copyOfPosition(position: Position): Position = Position(position.sourceIndex)
}

fun Sequence<Token>.toTransactional(): TokenSequence = TokenSequence(toList())