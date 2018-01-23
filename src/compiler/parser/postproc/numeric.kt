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

import compiler.ast.expression.NumericLiteralExpression
import compiler.lexer.NumericLiteralToken
import compiler.matching.ResultCertainty
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.rule.RuleMatchingResultImpl
import compiler.transact.Position
import compiler.transact.TransactionalSequence

fun NumericLiteralPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<NumericLiteralExpression> {
    return rule
        .flatten()
        .map(::toAST)
}

private fun toAST(matchingResult: RuleMatchingResult<TransactionalSequence<Any, Position>>): RuleMatchingResult<NumericLiteralExpression> {
    val numericToken = matchingResult.item?.next()!! as NumericLiteralToken

    return RuleMatchingResultImpl(
        ResultCertainty.DEFINITIVE,
        NumericLiteralExpression(numericToken),
        emptySet()
    )
}