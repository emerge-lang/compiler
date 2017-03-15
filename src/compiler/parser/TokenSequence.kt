package compiler.parser

import compiler.lexer.SourceLocation
import compiler.lexer.Token
import compiler.transact.Position
import compiler.transact.TransactionalSequence

class TokenSequence(val tokens: List<Token>, val initialSourceLocation: SourceLocation) : TransactionalSequence<Token, Position>(tokens)
{
    override var currentPosition: Position = Position(0)

    val currentSourceLocation: SourceLocation
        get() {
            var index = currentPosition.sourceIndex
            if (index > tokens.lastIndex) {
                index = tokens.lastIndex
            }

            return tokens.getOrNull(index)?.sourceLocation ?: initialSourceLocation
        }

    override fun copyOfPosition(position: Position): Position = Position(position.sourceIndex)
}

fun Sequence<Token>.toTransactional(initialSourceLocation: SourceLocation): TokenSequence = TokenSequence(toList(), initialSourceLocation)