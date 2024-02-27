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
import compiler.ast.Executable
import compiler.ast.Expression
import compiler.ast.IfExpression
import compiler.ast.TypeArgumentBundle
import compiler.ast.expression.ArrayLiteralExpression
import compiler.ast.expression.BooleanLiteralExpression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.NullLiteralExpression
import compiler.ast.expression.NumericLiteralExpression
import compiler.ast.expression.ParenthesisedExpression
import compiler.ast.expression.StringLiteralExpression
import compiler.ast.expression.UnaryExpression
import compiler.ast.type.TypeArgument
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.ELSE
import compiler.lexer.Keyword.IF
import compiler.lexer.KeywordToken
import compiler.lexer.NumericLiteralToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.StringLiteralContentToken
import compiler.lexer.TokenType
import compiler.parser.BinaryExpressionPostfix
import compiler.parser.ExpressionPostfix
import compiler.parser.InvocationExpressionPostfix
import compiler.parser.MemberAccessExpressionPostfix
import compiler.parser.NotNullExpressionPostfix
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.isolateCyclicGrammar
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.grammar.dsl.sequence
import compiler.parser.grammar.rule.Rule
import compiler.transact.TransactionalSequence

private val ExpressionBase: Rule<Expression> = eitherOf("expression without postfixes") {
    ref(UnaryExpression)
    ref(ValueExpression)
    ref(ParanthesisedExpression)
    ref(IfExpression)
}
    .astTransformation { tokens -> tokens.next() as Expression }

val Expression: Rule<Expression> = sequence("expression") {
    ref(ExpressionBase)
    repeating {
        ref(ExpressionPostfix)
    }
}
    .isolateCyclicGrammar
    .astTransformation(false, ::astTransformOneExpressionWithOptionalPostfixes)

val ExpressionExcludingBinaryPostfix = sequence("expression (excluding binary expressions)") {
    ref(ExpressionBase)
    repeating {
        ref(ExpressionPostfixExcludingBinary)
    }
}
    .astTransformation(false, ::astTransformOneExpressionWithOptionalPostfixes)

val StringLiteralExpression = sequence("string literal") {
    operator(Operator.STRING_DELIMITER)
    tokenOfType(TokenType.STRING_LITERAL_CONTENT)
    operator(Operator.STRING_DELIMITER)
}
    .astTransformation { tokens ->
        val startDelimiter = tokens.next() as OperatorToken
        val content = tokens.next() as StringLiteralContentToken
        val endDelimiter = tokens.next() as OperatorToken

        StringLiteralExpression(startDelimiter, content, endDelimiter)
    }

val ArrayLiteralExpression = sequence("array literal") {
    operator(Operator.SBRACE_OPEN)
    optional {
        ref(Expression)
        repeating {
            operator(Operator.COMMA)
            ref(Expression)
        }
    }
    operator(Operator.SBRACE_CLOSE)
}
    .astTransformation { tokens ->
        val openingBracket = tokens.next() as OperatorToken
        val elements = mutableListOf<Expression>()
        var next = tokens.next()
        while (next is Expression) {
            elements.add(next)
            next = tokens.next()
            check(next is OperatorToken)
            if (next.operator == Operator.SBRACE_CLOSE) {
                break
            }
            check(next.operator == Operator.COMMA)
            next = tokens.next()
        }
        val closingBracket = next as OperatorToken

        ArrayLiteralExpression(
            openingBracket,
            elements,
            closingBracket,
        )
    }

val LiteralExpression = sequence("literal") {
    eitherOf {
        tokenOfType(TokenType.NUMERIC_LITERAL)
        ref(StringLiteralExpression)
    }
}
    .astTransformation { tokens ->
        when (val valueToken = tokens.next()!!) {
            is NumericLiteralToken -> NumericLiteralExpression(valueToken)
            is StringLiteralExpression -> valueToken
            else -> throw InternalCompilerError("Unsupported literal value $valueToken")
        }
    }

val IdentifierExpression = sequence("identifier") {
    identifier()
}
    .astTransformation { tokens ->
        val identifier = tokens.next() as IdentifierToken
        when (identifier.value) {
            "true", "false" -> BooleanLiteralExpression(identifier.sourceLocation, identifier.value == "true")
            "null" -> NullLiteralExpression(identifier.sourceLocation)
            else -> IdentifierExpression(identifier)
        }
    }

val ValueExpression = eitherOf("value expression") {
    ref(LiteralExpression)
    ref(IdentifierExpression)
    ref(ArrayLiteralExpression)
}

val ParanthesisedExpression: Rule<Expression> = sequence("paranthesised expression") {
    operator(Operator.PARANT_OPEN)
    ref(Expression)
    operator(Operator.PARANT_CLOSE)
}
    .astTransformation { tokens ->
        val parantOpen = tokens.next()!! as OperatorToken
        val nested = tokens.next()!! as Expression

        ParenthesisedExpression(nested, parantOpen.sourceLocation)
    }

val UnaryExpression = sequence("unary expression") {
    eitherOf(Operator.PLUS, Operator.MINUS, Operator.EXCLAMATION_MARK)
    // TODO: tilde, ... what else?

    eitherOf {
        // TODO: reorder these to comply to the defined operator precedence (e.g. DOT before MINUS)
        ref(ValueExpression)
        ref(ParanthesisedExpression)
    }
}
    .astTransformation { tokens ->
        val operator = (tokens.next()!! as OperatorToken)
        val expression = tokens.next()!! as Expression
        UnaryExpression(operator, expression)
    }

val binaryOperators = arrayOf(
    // Arithmetic
    Operator.PLUS, Operator.MINUS, Operator.TIMES, Operator.DIVIDE,
    // Comparison
    Operator.EQUALS, Operator.GREATER_THAN, Operator.LESS_THAN, Operator.GREATER_THAN_OR_EQUALS, Operator.LESS_THAN_OR_EQUALS,
    Operator.IDENTITY_EQ, Operator.IDENTITY_NEQ,
    // MISC
    Operator.ELVIS
)

val BracedCodeOrSingleStatement = eitherOf("curly braced code or single statement") {
    sequence {
        operator(Operator.CBRACE_OPEN)
        optionalWhitespace()
        optional {
            ref(CodeChunk)
        }
        optionalWhitespace()
        operator(Operator.CBRACE_CLOSE)
    }
    ref(Expression)
}
    .astTransformation { tokens ->
        var next: Any? = tokens.next()

        if (next is Executable) {
            return@astTransformation next
        }

        if (next != OperatorToken(Operator.CBRACE_OPEN)) {
            throw InternalCompilerError("Unexpected $next, expecting ${Operator.CBRACE_OPEN} or executable")
        }

        next = tokens.next()

        if (next == OperatorToken(Operator.CBRACE_CLOSE)) {
            return@astTransformation CodeChunk(emptyList())
        }

        if (next !is CodeChunk) {
            throw InternalCompilerError("Unexpected $next, expecting code or ${Operator.CBRACE_CLOSE}")
        }

        return@astTransformation next
    }

val IfExpression = sequence("if-expression") {
    keyword(IF)
    ref(Expression)

    ref(BracedCodeOrSingleStatement)

    optionalWhitespace()

    optional {
        keyword(ELSE)
        optionalWhitespace()
        ref(BracedCodeOrSingleStatement)
    }
}
    .astTransformation { tokens ->
        val ifKeyword = tokens.next() as KeywordToken

        @Suppress("UNCHECKED_CAST")
        val condition = tokens.next() as Expression
        val thenCode: Executable = tokens.next() as Executable
        val elseCode: Executable? = if (tokens.hasNext()) {
            // skip ELSE keyword
            tokens.next()
            tokens.next() as Executable
        } else {
            null
        }

        IfExpression(
            ifKeyword.sourceLocation,
            condition,
            thenCode,
            elseCode
        )
    }

val ExpressionPostfixNotNull = sequence(OperatorToken(Operator.NOTNULL).toStringWithoutLocation()) {
    operator(Operator.NOTNULL)
    optionalWhitespace()
}
    .astTransformation { NotNullExpressionPostfix(it.next()!! as OperatorToken) }

val InvocationTypeArguments = sequence {
    /* this is the turbofish, stolen from Rust. Without the two COLONs, this source has two valid parse trees:
    A<Int>(false)

    Option 1:
    Binary(A, <, Binary(Int, >, Parenthesized(false)))

    Option 2:
    Invocation(name=A, typeArgs=[Int], args=[false])
    */
    operator(Operator.COLON)
    operator(Operator.COLON)
    ref(BracedTypeArguments)
}
    .astTransformation { tokens ->
        tokens.next()
        tokens.next()
        tokens.next() as TypeArgumentBundle
    }

val ExpressionPostfixInvocation = sequence("function invocation") {
    optional {
        ref(InvocationTypeArguments)
    }
    operator(Operator.PARANT_OPEN)
    optionalWhitespace()

    optional {
        ref(Expression)
        optionalWhitespace()

        repeating {
            operator(Operator.COMMA)
            optionalWhitespace()
            ref(Expression)
        }
    }

    optionalWhitespace()
    operator(Operator.PARANT_CLOSE)
}
    .astTransformation { tokens ->
        val typeArguments: List<TypeArgument>
        val next = tokens.next()!!
        if (next is TypeArgumentBundle) {
            typeArguments = next.arguments
            // skip PARANT_OPEN
            tokens.next() as OperatorToken
        } else {
            typeArguments = emptyList()
            // skip PARANT_OPEN
            next as OperatorToken
        }

        val valueArguments = mutableListOf<Expression>()
        while (tokens.peek() is Expression) {
            valueArguments.add(tokens.next()!! as Expression)

            // skip COMMA or PARANT_CLOSE
            tokens.next()!! as OperatorToken
        }

        InvocationExpressionPostfix(typeArguments, valueArguments)
    }

val ExpressionPostfixMemberAccess = sequence("member access") {
    eitherOf(Operator.DOT, Operator.SAFEDOT)
    identifier()
    optionalWhitespace()
}
    .astTransformation { tokens ->
        val accessOperator = tokens.next() as OperatorToken
        val memberNameToken = tokens.next() as IdentifierToken
        MemberAccessExpressionPostfix(accessOperator, memberNameToken)
    }

val ExpressionPostfixBinaryOperation = sequence("binary expression") {
    repeatingAtLeastOnce {
        eitherOf(*binaryOperators)
        ref(ExpressionExcludingBinaryPostfix)
    }
}
    .astTransformation { tokens ->
        BinaryExpressionPostfix(tokens.remainingToList())
    }

val ExpressionPostfixExcludingBinary = eitherOf {
    ref(ExpressionPostfixNotNull)
    ref(ExpressionPostfixInvocation)
    ref(ExpressionPostfixMemberAccess)
}

val ExpressionPostfix = eitherOf {
    ref(ExpressionPostfixExcludingBinary)
    ref(ExpressionPostfixBinaryOperation)
}
    .mapResult { it as ExpressionPostfix<Expression> }

private fun astTransformOneExpressionWithOptionalPostfixes(tokens: TransactionalSequence<Any, *>): Expression {
    val expression = tokens.next()!! as Expression
    return tokens
        .remainingToList()
        .fold(expression) { expr, postfix -> (postfix as ExpressionPostfix<*>).modify(expr) }
}