package compiler.parser

import compiler.lexer.SourceLocation
import compiler.lexer.Token
import compiler.transact.Position
import compiler.transact.TransactionalSequence

class TokenSequence(val tokens: List<Token>) : TransactionalSequence<Token, Position>(tokens)
{
    override var currentPosition: Position = Position(0)

    val currentSourceLocation: SourceLocation
        get() {
            var index = currentPosition.sourceIndex
            if (index > tokens.lastIndex) {
                index = tokens.lastIndex
            }

            return tokens.getOrNull(index)!!.sourceLocation!!
        }

    /** Returns the next token in the seuqence (see [peek]), or the last if the end of the sequence has been reached. */
    fun peekOrLast(): Token {
        return peek() ?: tokens.last()
    }

    override fun copyOfPosition(position: Position): Position = Position(position.sourceIndex)
}

fun Sequence<Token>.toTransactional(): TokenSequence = TokenSequence(toList())