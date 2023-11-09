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

import compiler.ast.AssignmentStatement
import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.matching.ResultCertainty.DEFINITIVE
import compiler.matching.ResultCertainty.MATCHED
import compiler.matching.ResultCertainty.OPTIMISTIC
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.CodeChunkPostProcessor
import compiler.parser.postproc.ExpressionPostprocessor
import compiler.parser.postproc.ReturnStatementPostProcessor
import compiler.parser.postproc.flatten
import compiler.parser.postproc.mapResult
import compiler.parser.postproc.toAST_AssignmentStatement
import compiler.parser.rule.Rule

val ReturnStatement = sequence("return statement") {
    keyword(Keyword.RETURN)
    certainty = MATCHED
    ref(Expression)
    certainty = DEFINITIVE
}
    .postprocess(::ReturnStatementPostProcessor)

val Assignable = sequence("assignable") {
    eitherOf {
        ref(BinaryExpression)
        ref(UnaryExpression)
        sequence {
            ref(ParanthesisedExpression)
            certainty = MATCHED
            ref(ExpressionPostfix)
        }
        ref(IdentifierExpression)
    }
    certainty = MATCHED
    atLeast(0) {
        ref(ExpressionPostfix)
    }
    certainty = DEFINITIVE
}
    .postprocess(::ExpressionPostprocessor)

val AssignmentStatement: Rule<AssignmentStatement> = sequence("assignment") {
    ref(Assignable)

    operator(Operator.ASSIGNMENT)
    certainty = MATCHED

    ref(Expression)
    certainty = DEFINITIVE
}
    .flatten()
    .mapResult(::toAST_AssignmentStatement)

val LineOfCode = sequence {
    eitherOf {
        ref(VariableDeclaration)
        ref(AssignmentStatement)
        ref(ReturnStatement)
        ref(Expression)
    }
    certainty = MATCHED

    atLeast(0) {
        operator(Operator.NEWLINE)
        certainty = MATCHED
    }
    certainty = DEFINITIVE
}

val CodeChunk = sequence {
    certainty = MATCHED
    optionalWhitespace()
    optional {
        ref(LineOfCode)
        certainty = MATCHED

        atLeast(0) {
            ref(LineOfCode)
            certainty = DEFINITIVE
        }
        certainty = DEFINITIVE
    }

    certainty = OPTIMISTIC
}
    .postprocess(::CodeChunkPostProcessor)
