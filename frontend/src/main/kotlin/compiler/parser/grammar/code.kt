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

import compiler.InternalCompilerError
import compiler.ast.CodeChunk
import compiler.ast.Expression
import compiler.ast.ReturnStatement
import compiler.ast.Statement
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.Rule

val ReturnStatement = sequence("return statement") {
    keyword(Keyword.RETURN)
    optional {
        ref(Expression)
    }
}
    .astTransformation { tokens ->
        val keyword = tokens.next()!! as KeywordToken
        val expression = if (tokens.hasNext()) tokens.next()!! as Expression else null

        ReturnStatement(keyword, expression)
    }

val Assignable = sequence("assignable") {
    // TODO: refine grammar
    ref(ExpressionExcludingBinaryPostfix)
}
    .astTransformation { tokens ->
        val expression = tokens.next()!! as Expression
        expression
    }

val LineOfCode = sequence {
    eitherOf {
        ref(VariableDeclaration)
        ref(ReturnStatement)
        ref(Expression)
    }

    repeating {
        operator(Operator.NEWLINE)
    }
}
    .astTransformation { tokens -> tokens.next() as Statement }

val CodeChunk: Rule<CodeChunk> = sequence("a chunk of code") {
    optionalWhitespace()
    optional {
        ref(LineOfCode)

        repeating {
            ref(LineOfCode)
        }
    }
}
    .astTransformation { tokens ->
        tokens.remainingToList()
            .map { it as? Statement ?: throw InternalCompilerError("How did this thing get into here?!") }
            .let(::CodeChunk)
    }
