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

package compiler.parser.grammar;

import compiler.lexer.Keyword.VAL
import compiler.lexer.Keyword.VAR
import compiler.lexer.Operator.*
import compiler.matching.ResultCertainty.DEFINITIVE
import compiler.matching.ResultCertainty.MATCHED
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.ModulePostProcessor
import compiler.parser.postproc.ParameterDeclarationPostProcessor
import compiler.parser.postproc.ParameterListPostprocessor

val Parameter = sequence {

    optional {
        ref(TypeModifier)
    }

    optional {
        eitherOf {
            keyword(VAR)
            keyword(VAL)
        }
    }

    identifier()

    optional {
        operator(COLON)
        ref(Type)
    }
}
    .describeAs("parameter declaration")
    .postprocess(::ParameterDeclarationPostProcessor)

val ParameterList = sequence {
    operator(PARANT_OPEN)

    optionalWhitespace()

    optional {
        ref(Parameter)

        optionalWhitespace()

        atLeast(0) {
            operator(COMMA)
            optionalWhitespace()
            ref(Parameter)
        }
    }

    optionalWhitespace()
    operator(PARANT_CLOSE)
}
    .describeAs("parenthesised paramete rlist")
    .postprocess(::ParameterListPostprocessor)



val Module = sequence {
    certainty = MATCHED
    atLeast(0) {
        optionalWhitespace()
        eitherOf(mismatchCertainty = DEFINITIVE) {
            ref(ModuleDeclaration)
            ref(ImportDeclaration)
            ref(VariableDeclaration)
            ref(StandaloneFunctionDeclaration)
            endOfInput()
        }
        certainty = DEFINITIVE
    }
}
    .describeAs("module")
    .postprocess(::ModulePostProcessor)