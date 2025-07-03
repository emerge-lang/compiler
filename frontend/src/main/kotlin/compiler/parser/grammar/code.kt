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
import compiler.ast.AstCodeChunk
import compiler.ast.AstDoWhileLoop
import compiler.ast.AstForEachLoop
import compiler.ast.AstMixinStatement
import compiler.ast.AstWhileLoop
import compiler.ast.Statement
import compiler.lexer.DelimitedIdentifierContentToken
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.IdentifierTokenRule
import compiler.parser.grammar.rule.Rule
import compiler.ast.Expression as AstExpression

val Identifier = eitherOf("identifier") {
    ref(IdentifierTokenRule)
    sequence {
        operator(Operator.IDENTIFIER_DELIMITER)
        delimitedIdentifierContent()
        operator(Operator.IDENTIFIER_DELIMITER)
    }
}
    .astTransformation { tokens ->
        val first = tokens.next()!!
        if (first is IdentifierToken) {
            return@astTransformation first
        }
        first as OperatorToken

        val content = tokens.next()!! as DelimitedIdentifierContentToken
        val endDelimiter = tokens.next()!! as OperatorToken
        IdentifierToken(content.content, first.span .. endDelimiter.span)
    }

val AssignmentStatement = sequence("assignment statement") {
    keyword(Keyword.SET)
    ref(Expression)
    operator(Operator.ASSIGNMENT)
    ref(Expression)
}
    .astTransformation { tokens ->
        val setKeyword = tokens.next()!! as KeywordToken
        val target = tokens.next()!! as AstExpression
        val assignmentOperator = tokens.next()!! as OperatorToken
        val value = tokens.next()!! as AstExpression

        AssignmentStatement(setKeyword, target, assignmentOperator, value)
    }

val WhileLoop = sequence("while loop") {
    keyword(Keyword.WHILE)
    ref(Expression)
    ref(CurlyBracedCodeChunk)
}
    .astTransformation { tokens ->
        val whileKeyword = tokens.next()!! as KeywordToken
        val condition = tokens.next()!! as AstExpression
        val body = tokens.next()!! as AstCodeChunk
        AstWhileLoop(
            whileKeyword.span .. condition.span,
            condition,
            body,
        )
    }

val DoWhileLoop = sequence("do-while loop") {
    keyword(Keyword.DO)
    ref(CurlyBracedCodeChunk)
    keyword(Keyword.WHILE)
    ref(Expression)
}
    .astTransformation { tokens ->
        val doKeyword = tokens.next() as KeywordToken
        val body = tokens.next() as AstCodeChunk
        tokens.next()!! // skip while keyword
        val condition = tokens.next() as AstExpression

        AstDoWhileLoop(
            doKeyword.span .. condition.span,
            condition,
            body,
        )
    }

val ForEachLoop = sequence("foreach loop") {
    keyword(Keyword.FOREACH)
    ref(Identifier)
    keyword(Keyword.IN)
    ref(Expression)
    ref(CurlyBracedCodeChunk)
}
    .astTransformation { tokens ->
        val foreachKeyword = tokens.next() as KeywordToken
        val cursorVariableName = tokens.next() as IdentifierToken
        val inKeyword = tokens.next() as KeywordToken
        val iterableExpression = tokens.next() as AstExpression
        val body = tokens.next() as AstCodeChunk

        AstForEachLoop(
            foreachKeyword,
            cursorVariableName,
            inKeyword,
            iterableExpression,
            body,
        )
    }

val MixinStatement = sequence("mixin statement") {
    keyword(Keyword.MIXIN)
    ref(Expression)
}
    .astTransformation { tokens ->
        val mixinKeyword = tokens.next() as KeywordToken
        val value = tokens.next() as AstExpression
        AstMixinStatement(mixinKeyword, value)
    }

val LineOfCode = sequence {
    eitherOf {
        ref(AssignmentStatement)
        ref(ReturnStatement)
        ref(ThrowStatement)
        ref(VariableDeclaration)
        ref(Expression)
        ref(WhileLoop)
        ref(DoWhileLoop)
        ref(ForEachLoop)
        ref(MixinStatement)
    }

    operator(Operator.NEWLINE)
}
    .astTransformation { tokens -> tokens.next() as Statement }

val CurlyBracedCodeChunk: Rule<AstCodeChunk> = sequence("a chunk of code wrapped by curly braces") {
    operator(Operator.CBRACE_OPEN)
    repeating {
        ref(LineOfCode)
    }
    operator(Operator.CBRACE_CLOSE)
}
    .astTransformation { tokens ->
        val cbraceOpen = tokens.next() as OperatorToken
        val statements = tokens.takeWhileIsInstanceOf<Statement>()
        val cbraceClose = tokens.next() as OperatorToken

        AstCodeChunk(statements, cbraceOpen.span .. cbraceClose.span)
    }