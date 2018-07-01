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

import compiler.ast.ImportDeclaration
import compiler.lexer.IdentifierToken
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.reportings.Reporting
import compiler.reportings.TokenMismatchReporting
import compiler.transact.Position
import compiler.transact.TransactionalSequence
import java.util.*

fun ImportPostprocessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<ImportDeclaration> {
    return rule

    // enhance error for "import xyz"
    .enhanceErrors(
        { it is TokenMismatchReporting && it.expected == OperatorToken(Operator.DOT) && it.actual == OperatorToken(Operator.NEWLINE) },
        { _it ->
            val it = _it as TokenMismatchReporting
            Reporting.parsingError("${it.message}; To import all exports of the module write module.*", it.actual.sourceLocation)
        }
    )
    .flatten()
    .trimWhitespaceTokens()
    .mapResult(::toAST_import)
}

private fun toAST_import(tokens: TransactionalSequence<Any, Position>): ImportDeclaration {
    val keyword = tokens.next()!! as KeywordToken

    val identifiers = ArrayList<IdentifierToken>()

    while (tokens.hasNext()) {
        // collect the identifier
        identifiers.add(tokens.next()!! as IdentifierToken)

        // skip the dot, if there
        tokens.next()
    }

    return ImportDeclaration(keyword.sourceLocation, identifiers)
}