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

import compiler.ast.ASTVisibilityModifier
import compiler.ast.expression.Expression
import compiler.ast.struct.StructDeclaration
import compiler.ast.struct.StructMemberDeclaration
import compiler.ast.type.TypeReference
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun StructMemberDeclarationPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<StructMemberDeclaration> {
    return rule
        .flatten()
        .trimWhitespaceTokens()
        .mapResult(::toAST_StructMemberDeclaration)
}

private fun toAST_StructMemberDeclaration(tokens: TransactionalSequence<Any, Position>): StructMemberDeclaration {
    var next = tokens.next()!!

    val visibilityModifier = if (next is ASTVisibilityModifier) {
        val _t = next
        next = tokens.next()!!
        _t
    } else ASTVisibilityModifier.DEFAULT

    val name = next as IdentifierToken

    tokens.next()!! as OperatorToken // skip OPERATOR_COLON

    val type = tokens.next()!! as TypeReference

    val defaultValue = if (tokens.hasNext()) {
        // default value is present
        tokens.next()!! as OperatorToken // EQUALS
        tokens.next()!! as Expression<*>?
    } else null

    return StructMemberDeclaration(
        name.sourceLocation,
        visibilityModifier,
        name,
        type,
        defaultValue
    )
}

fun StructDeclarationPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<StructDeclaration> {
    return rule
        .flatten()
        .mapResult(::toAST_StructDeclaration)
}

private fun toAST_StructDeclaration(tokens: TransactionalSequence<Any, Position>): StructDeclaration {
    val declarationKeyword = tokens.next()!! as KeywordToken // struct keyword

    val name = tokens.next()!! as IdentifierToken

    tokens.next()!! as OperatorToken // CBRACE_OPEN

    val memberDeclarations = mutableSetOf<StructMemberDeclaration>()

    var next = tokens.next()!! // until CBRACE_CLOSE
    while (next is StructMemberDeclaration) {
        memberDeclarations += next
        next = tokens.next()!! as OperatorToken

        if (next.operator == Operator.NEWLINE) {
            next = tokens.next()!!
        }
    }

    return StructDeclaration(
        declarationKeyword.sourceLocation,
        name,
        memberDeclarations
    )
}