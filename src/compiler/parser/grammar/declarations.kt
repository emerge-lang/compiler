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

package compiler.parser.grammar

import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.matching.ResultCertainty
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.VariableDeclarationPostProcessor

val VariableDeclaration = sequence {

    optional {
        ref(TypeModifier)
    }

    optionalWhitespace()

    eitherOf {
        keyword(Keyword.VAR)
        keyword(Keyword.VAL)
    }
    certainty = ResultCertainty.MATCHED

    optionalWhitespace()

    identifier()
    certainty = ResultCertainty.OPTIMISTIC

    optional {
        operator(Operator.COLON)
        ref(Type)
    }

    optional {
        optionalWhitespace()
        operator(Operator.ASSIGNMENT)
        certainty = ResultCertainty.DEFINITIVE
        ref(Expression)
    }

    certainty = ResultCertainty.DEFINITIVE
}
    .describeAs("variable declaration")
    .postprocess(::VariableDeclarationPostProcessor)

