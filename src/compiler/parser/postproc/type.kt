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

/**
 *
 */
package compiler.parser.postproc

import compiler.InternalCompilerError
import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.lexer.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun TypePostprocessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<TypeReference> {
    return rule
        .flatten()
        .mapResult(::toAST)
}

private fun toAST(tokens: TransactionalSequence<Any, Position>): TypeReference {
    val nameOrModifier = tokens.next()!!

    val typeModifier: TypeModifier?
    val nameToken: IdentifierToken

    if (nameOrModifier is TypeModifier) {
        typeModifier = nameOrModifier
        nameToken = tokens.next()!! as IdentifierToken
    }
    else {
        typeModifier = null
        nameToken = nameOrModifier as IdentifierToken
    }

    val isNullable = tokens.hasNext() && tokens.next()!! == OperatorToken(Operator.QUESTION_MARK)

    return TypeReference(nameToken, isNullable, typeModifier)
}


fun TypeModifierPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<TypeModifier> {
    return rule
        .flatten()
        .mapResult { tokens ->
            val keyword = (tokens.next() as KeywordToken?)?.keyword
            when(keyword) {
                Keyword.MUTABLE   -> TypeModifier.MUTABLE
                Keyword.READONLY  -> TypeModifier.READONLY
                Keyword.IMMUTABLE -> TypeModifier.IMMUTABLE
                else -> throw InternalCompilerError("$keyword is not a type modifier")
            }
        }
}