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

package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.AssignmentStatement
import compiler.ast.CodeChunk
import compiler.ast.Executable
import compiler.ast.ReturnStatement
import compiler.ast.expression.Expression
import compiler.lexer.KeywordToken
import compiler.lexer.OperatorToken
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun ReturnStatementPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<ReturnStatement> {
    return rule
        .flatten()
        .mapResult(::toAST_ReturnStatement)
}

private fun toAST_ReturnStatement(input: TransactionalSequence<Any, Position>): ReturnStatement {
    val keyword = input.next()!! as KeywordToken
    val expression = input.next()!! as Expression<*>

    return ReturnStatement(keyword, expression)
}

// ------

fun toAST_AssignmentStatement(input: TransactionalSequence<Any, Position>): AssignmentStatement {
    val targetExpression   = input.next() as Expression<*>
    val assignmentOperator = input.next() as OperatorToken
    val valueExpression    = input.next() as Expression<*>

    return AssignmentStatement(targetExpression, assignmentOperator, valueExpression)
}

// ------

fun CodeChunkPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<CodeChunk> {
    return rule
        .flatten()
        .mapResult(::toAST_codeChunk)
}

private fun toAST_codeChunk(input: TransactionalSequence<Any, Position>): CodeChunk {
    val executables = mutableListOf<Executable<*>>()
    input.remainingToList()
        .filter { it !is OperatorToken }
        .forEach {
            if (it is Executable<*>) {
                executables.add(it)
            }
            else throw InternalCompilerError("How did this thing get into here?!")
        }

    return CodeChunk(executables)
}