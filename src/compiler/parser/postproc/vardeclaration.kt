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

import compiler.ast.VariableDeclaration
import compiler.ast.expression.Expression
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.lexer.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun VariableDeclarationPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<VariableDeclaration> {
    return rule
        .flatten()
        .mapResult(::toAST_VariableDeclaration)
}

private fun toAST_VariableDeclaration(input: TransactionalSequence<Any, Position>): VariableDeclaration {
    var modifierOrKeyword = input.next()!!

    val typeModifier: TypeModifier?
    val declarationKeyword: KeywordToken

    if (modifierOrKeyword is TypeModifier) {
        typeModifier = modifierOrKeyword
        declarationKeyword = input.next()!! as KeywordToken
    }
    else {
        typeModifier = null
        declarationKeyword = modifierOrKeyword as KeywordToken
    }

    val name = input.next()!! as IdentifierToken

    var type: TypeReference? = null

    var colonOrEqualsOrNewline = input.next()

    if (colonOrEqualsOrNewline == OperatorToken(Operator.COLON)) {
        type = input.next()!! as TypeReference
        colonOrEqualsOrNewline = input.next()!!
    }

    var assignExpression: Expression<*>? = null

    val equalsOrNewline = colonOrEqualsOrNewline

    if (equalsOrNewline == OperatorToken(Operator.ASSIGNMENT)) {
        assignExpression = input.next()!! as Expression<*>
    }

    return VariableDeclaration(
        declarationKeyword.sourceLocation,
        typeModifier,
        name,
        type,
        declarationKeyword.keyword == Keyword.VAR,
        assignExpression
    )
}