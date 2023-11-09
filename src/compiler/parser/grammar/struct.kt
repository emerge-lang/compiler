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

import compiler.lexer.Keyword.STRUCT_DEFINITION
import compiler.lexer.Operator.*
import compiler.matching.ResultCertainty.DEFINITIVE
import compiler.matching.ResultCertainty.MATCHED
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.StructDeclarationPostProcessor
import compiler.parser.postproc.StructMemberDeclarationPostProcessor

val StructMemberDefinition = sequence("struct member declaration") {
    optional {
        ref(VisibilityModifier)
    }

    optionalWhitespace()

    identifier()
    certainty = DEFINITIVE

    operator(COLON)
    ref(Type)

    optional {
        optionalWhitespace()
        operator(ASSIGNMENT)
        certainty = DEFINITIVE
        ref(Expression)
    }
}
    .postprocess(::StructMemberDeclarationPostProcessor)

val StructDefinition = sequence("struct definition") {
    keyword(STRUCT_DEFINITION)
    certainty = MATCHED
    optionalWhitespace()
    identifier()
    optionalWhitespace()
    // TODO: add struct generics

    operator(CBRACE_OPEN)
    optionalWhitespace()

    optional {
        ref(StructMemberDefinition)
    }
    atLeast(0) {
        operator(NEWLINE)
        ref(StructMemberDefinition)
    }

    optionalWhitespace()
    operator(CBRACE_CLOSE)
}
    .postprocess(::StructDeclarationPostProcessor)