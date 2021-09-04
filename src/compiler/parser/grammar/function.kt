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
import compiler.parser.postproc.FunctionModifierPostProcessor
import compiler.parser.postproc.ParameterDeclarationPostProcessor
import compiler.parser.postproc.ParameterListPostprocessor
import compiler.parser.postproc.StandaloneFunctionPostprocessor

val Parameter = sequence {

    optional {
        ref(TypeModifier)
    }

    optional {
        eitherOf {
            keyword(Keyword.VAR)
            keyword(Keyword.VAL)
        }
    }

    identifier()

    optional {
        operator(Operator.COLON)
        ref(Type)
    }
}
    .describeAs("parameter declaration")
    .postprocess(::ParameterDeclarationPostProcessor)
val ParameterList = sequence {
    operator(Operator.PARANT_OPEN)

    optionalWhitespace()

    optional {
        ref(Parameter)

        optionalWhitespace()

        atLeast(0) {
            operator(Operator.COMMA)
            optionalWhitespace()
            ref(Parameter)
        }
    }

    optionalWhitespace()
    operator(Operator.PARANT_CLOSE)
}
    .describeAs("parenthesised paramete rlist")
    .postprocess(::ParameterListPostprocessor)

val FunctionModifier = sequence {
    eitherOf {
        keyword(Keyword.READONLY)
        keyword(Keyword.NOTHROW)
        keyword(Keyword.PURE)
        keyword(Keyword.OPERATOR)
        keyword(Keyword.EXTERNAL)
    }
    certainty = ResultCertainty.DEFINITIVE
}
    .postprocess(::FunctionModifierPostProcessor)

val StandaloneFunctionDeclaration = sequence {
    atLeast(0) {
        ref(FunctionModifier)
    }

    keyword(Keyword.FUNCTION)

    certainty = ResultCertainty.MATCHED

    optional {
        ref(Type)
        operator(Operator.DOT)
    }

    optionalWhitespace()
    identifier()
    optionalWhitespace()
    ref(ParameterList)
    optionalWhitespace()

    optional {
        operator(Operator.RETURNS)
        optionalWhitespace()
        ref(Type)
    }

    certainty = ResultCertainty.OPTIMISTIC

    eitherOf {
        sequence {
            optionalWhitespace()
            operator(Operator.CBRACE_OPEN)
            certainty = ResultCertainty.DEFINITIVE
            ref(CodeChunk)
            optionalWhitespace()
            operator(Operator.CBRACE_CLOSE)
        }
        sequence {
            operator(Operator.ASSIGNMENT)
            certainty = ResultCertainty.DEFINITIVE
            ref(Expression)
            eitherOf {
                operator(Operator.NEWLINE)
                endOfInput()
            }
        }
        operator(Operator.NEWLINE)
        endOfInput()
    }

    certainty = ResultCertainty.DEFINITIVE
}
    .describeAs("function declaration")
    .postprocess(::StandaloneFunctionPostprocessor)
