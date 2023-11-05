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
import compiler.ast.ParameterList
import compiler.ast.VariableDeclaration
import compiler.ast.expression.Expression
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.lexer.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun ParameterDeclarationPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<VariableDeclaration> {
    return rule
        .flatten()
        .mapResult(::toAST_ParameterDeclaration)
}

private fun toAST_ParameterDeclaration(input: TransactionalSequence<Any, Position>): VariableDeclaration {
    var declarationKeyword: Keyword? = null
    var typeModifier: TypeModifier? = null
    var name: IdentifierToken
    var type: TypeReference? = null
    var initializer: Expression<*>? = null

    var next = input.next()!!

    if (next is KeywordToken) {
        declarationKeyword = next.keyword
        next = input.next()!!
    }

    if (next is TypeModifier) {
        typeModifier = next
        next = input.next()!!
    }

    name = next as IdentifierToken

    if (input.peek() == OperatorToken(Operator.COLON)) {
        input.next()
        type = input.next()!! as TypeReference
    }

    if (input.peek() == OperatorToken(Operator.ASSIGNMENT)) {
        input.next()
        initializer = input.next()!! as Expression<*>
    }

    return VariableDeclaration(
        name.sourceLocation,
        typeModifier,
        name,
        type,
        declarationKeyword == Keyword.VAR,
        initializer,
    )
}

fun ParameterListPostprocessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<ParameterList> {
    return rule
        .flatten()
        .mapResult(::toAST_ParameterList)
}

private fun toAST_ParameterList(tokens: TransactionalSequence<Any, Position>): ParameterList {
    // skip PARANT_OPEN
    tokens.next()!!

    val parameters: MutableList<VariableDeclaration> = LinkedList()

    while (tokens.hasNext()) {
        var next = tokens.next()!!
        if (next == OperatorToken(Operator.PARANT_CLOSE)) {
            return ParameterList(parameters)
        }

        parameters.add(next as VariableDeclaration)

        tokens.mark()

        next = tokens.next()!!
        if (next == OperatorToken(Operator.PARANT_CLOSE)) {
            tokens.commit()
            return ParameterList(parameters)
        }

        if (next == OperatorToken(Operator.COMMA)) {
            tokens.commit()
        }
        else if (next !is VariableDeclaration) {
            tokens.rollback()
            next as Token
            throw InternalCompilerError("Unexpected ${next.toStringWithoutLocation()} in parameter list, expecting OPERATOR PARANT_CLOSE or OPERATOR COMMA")
        }
    }

    throw InternalCompilerError("This line should never have been reached :(")
}
