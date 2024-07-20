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

package compiler.ast

import compiler.ast.Statement.Companion.chain
import compiler.binding.BoundCodeChunk
import compiler.binding.context.ExecutionScopedCTContext
import compiler.lexer.Span

/**
 * A piece of executable code
 */
class AstCodeChunk(
    val statements: List<Statement>
) : Expression {
    override val span: Span = statements.firstOrNull()?.span ?: Span.UNKNOWN

    /*
    fun bindTo(context: CTContext): BoundCodeChunk {
        val initialContext = context as? ExecutionScopedCTContext ?: throw InternalCompilerError("Can this ever happen? If yes: easy fix right here")
        val boundStatements = statements.chain(initialContext).toList()
        return BoundCodeChunk(context, this, boundStatements)
    }
     */

    override fun bindTo(context: ExecutionScopedCTContext): BoundCodeChunk {
        val boundStatements = statements.chain(context).toList()
        return BoundCodeChunk(context, this, boundStatements)
    }
}