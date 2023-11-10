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
import compiler.ast.AssignmentStatement
import compiler.ast.CodeChunk
import compiler.ast.Executable
import compiler.ast.ReturnStatement
import compiler.ast.expression.Expression
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.Rule
import compiler.parser.ExpressionPostfix
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.sequence

val ReturnStatement = sequence("return statement") {
    keyword(Keyword.RETURN)
    __unambiguous()
    ref(Expression)
}
    .astTransformation { tokens ->
        val keyword = tokens.next()!! as KeywordToken
        val expression = tokens.next()!! as Expression<*>

        ReturnStatement(keyword, expression)
    }

val Assignable = sequence("assignable") {
    eitherOf {
        ref(BinaryExpression)
        ref(UnaryExpression)
        sequence {
            ref(ParanthesisedExpression)
            __unambiguous()
            ref(ExpressionPostfix)
        }
        ref(IdentifierExpression)
    }
    __unambiguous()
    atLeast(0) {
        ref(ExpressionPostfix)
    }
}
    .astTransformation { tokens ->
        val expression = tokens.next()!! as Expression<*>
        tokens
            .remainingToList()
            .fold(expression) { expr, postfix -> (postfix as ExpressionPostfix<*>).modify(expr) }
    }

val AssignmentStatement: Rule<AssignmentStatement> = sequence("assignment") {
    ref(Assignable)
    operator(Operator.ASSIGNMENT)
    __unambiguous()
    ref(Expression)
}
    .astTransformation { tokens ->
        val targetExpression   = tokens.next() as Expression<*>
        val assignmentOperator = tokens.next() as OperatorToken
        val valueExpression    = tokens.next() as Expression<*>

        AssignmentStatement(targetExpression, assignmentOperator, valueExpression)
    }

val LineOfCode = sequence {
    eitherOf {
        ref(VariableDeclaration)
        ref(AssignmentStatement)
        ref(ReturnStatement)
        ref(Expression)
    }
    __unambiguous()

    atLeast(0) {
        operator(Operator.NEWLINE)
        __unambiguous()
    }
}

val CodeChunk = sequence {
    __unambiguous()
    optionalWhitespace()
    optional {
        ref(LineOfCode)
        __unambiguous()

        atLeast(0) {
            ref(LineOfCode)
            __unambiguous()
        }
    }
}
    .astTransformation { tokens ->
        tokens.remainingToList()
            .filter { it !is OperatorToken }
            .map { it as? Executable<*> ?: throw InternalCompilerError("How did this thing get into here?!") }
            .let(::CodeChunk)
    }
