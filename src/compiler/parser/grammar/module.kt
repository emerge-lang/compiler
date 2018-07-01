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
import compiler.parser.postproc.ImportPostprocessor
import compiler.parser.postproc.ModuleDeclarationPostProcessor
import compiler.parser.postproc.ModuleNamePostProcessor
import compiler.parser.postproc.ModulePostProcessor

val ModuleName = sequence {
    identifier()

    certainty = ResultCertainty.OPTIMISTIC

    atLeast(0) {
        operator(Operator.DOT)
        certainty = ResultCertainty.MATCHED
        identifier()
    }
}
        .describeAs("module or package name")
        .postprocess(::ModuleNamePostProcessor)

val ModuleDeclaration = sequence {
    keyword(Keyword.MODULE)

    certainty = ResultCertainty.MATCHED

    ref(ModuleName)

    operator(Operator.NEWLINE)
}
    .describeAs("module declaration")
    .postprocess(::ModuleDeclarationPostProcessor)

val ImportDeclaration = sequence {
    keyword(Keyword.IMPORT)

    certainty = ResultCertainty.MATCHED

    atLeast(1) {
        identifier()
        operator(Operator.DOT)
    }
    certainty = ResultCertainty.OPTIMISTIC
    identifier(acceptedOperators = listOf(Operator.TIMES))
    operator(Operator.NEWLINE)
}
    .describeAs("import declaration")
    .postprocess(::ImportPostprocessor)
val Module = sequence {
    certainty = ResultCertainty.MATCHED
    atLeast(0) {
        optionalWhitespace()
        eitherOf(mismatchCertainty = ResultCertainty.DEFINITIVE) {
            ref(ModuleDeclaration)
            ref(ImportDeclaration)
            ref(VariableDeclaration)
            ref(StandaloneFunctionDeclaration)
            ref(StructDefinition)
            endOfInput()
        }
        certainty = ResultCertainty.DEFINITIVE
    }
}
    .describeAs("module")
    .postprocess(::ModulePostProcessor)