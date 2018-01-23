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