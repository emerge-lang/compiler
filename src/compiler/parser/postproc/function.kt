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
import compiler.ast.CodeChunk
import compiler.ast.FunctionDeclaration
import compiler.ast.ParameterList
import compiler.ast.ReturnStatement
import compiler.ast.expression.Expression
import compiler.ast.type.FunctionModifier
import compiler.ast.type.TypeReference
import compiler.lexer.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun StandaloneFunctionPostprocessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<FunctionDeclaration> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): FunctionDeclaration {
    val modifiers = mutableSetOf<FunctionModifier>()
    var next: Any? = tokens.next()!!
    while (next is FunctionModifier) {
        modifiers.add(next)
        next = tokens.next()!!
    }

    val declarationKeyword = next as KeywordToken

    val receiverType: TypeReference?
    next = tokens.next()!!
    if (next is TypeReference) {
        receiverType = next
        // skip DOT
        tokens.next()

        next = tokens.next()!!
    }
    else {
        receiverType = null
    }

    val name = next as IdentifierToken
    val parameterList = tokens.next()!! as ParameterList

    next = tokens.next()!!

    var type: TypeReference? = null

    if (next == OperatorToken(Operator.RETURNS)) {
        type = tokens.next()!! as TypeReference
        next = tokens.next()
    }

    if (next == OperatorToken(Operator.CBRACE_OPEN)) {
        val code = tokens.next()!! as CodeChunk
        // ignore trailing CBRACE_CLOSE

        return FunctionDeclaration(declarationKeyword.sourceLocation, modifiers, receiverType, name, parameterList, type, code)
    }
    else if (next == OperatorToken(Operator.ASSIGNMENT)) {
        val assignmentOp: OperatorToken = next as OperatorToken
        val singleExpression = tokens.next()!! as Expression<*>

        val expressionAsCode = CodeChunk(
            listOf(
                ReturnStatement(
                    KeywordToken(Keyword.RETURN, "=", assignmentOp.sourceLocation),
                    singleExpression
                )
            )
        )

        return FunctionDeclaration(
            declarationKeyword.sourceLocation,
            modifiers,
            receiverType,
            name,
            parameterList,
            type,
            expressionAsCode
        )
    }
    else if (next == OperatorToken(Operator.NEWLINE) || next == null) {
        // function without body with trailing newline or immediately followed by EOF
        return FunctionDeclaration(declarationKeyword.sourceLocation, modifiers, receiverType, name, parameterList, type, null)
    }
    else {
        throw InternalCompilerError("Unexpected token when building AST: expected ${OperatorToken(Operator.CBRACE_OPEN)} or ${OperatorToken(Operator.ASSIGNMENT)} but got $next")
    }
}