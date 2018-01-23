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
import compiler.ast.type.FunctionModifier
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult

fun FunctionModifierPostProcessor(rule: Rule<List<RuleMatchingResult<*>>>): Rule<FunctionModifier> {
    return rule
        .flatten()
        .mapResult { tokens -> when((tokens.next()!! as KeywordToken).keyword) {
            Keyword.READONLY -> FunctionModifier.READONLY
            Keyword.NOTHROW  -> FunctionModifier.NOTHROW
            Keyword.PURE     -> FunctionModifier.PURE
            Keyword.OPERATOR -> FunctionModifier.OPERATOR
            Keyword.EXTERNAL -> FunctionModifier.EXTERNAL
            else             -> throw InternalCompilerError("Keyword is not a function modifier")
        }}
}