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
import compiler.ast.expression.BinaryExpression
import compiler.ast.expression.BooleanLiteralExpression
import compiler.ast.expression.Expression
import compiler.ast.expression.IdentifierExpression
import compiler.ast.expression.IfExpression
import compiler.ast.expression.NumericLiteralExpression
import compiler.ast.expression.ParenthesisedExpression
import compiler.ast.expression.UnaryExpression
import compiler.binding.expression.BoundExpression
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.ELSE
import compiler.lexer.Keyword.IF
import compiler.lexer.KeywordToken
import compiler.lexer.NumericLiteralToken
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.TokenType
import compiler.matching.ResultCertainty.DEFINITIVE
import compiler.matching.ResultCertainty.MATCHED
import compiler.matching.ResultCertainty.OPTIMISTIC
import compiler.parser.grammar.dsl.astTransformation
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.sequence
import compiler.parser.ExpressionPostfix
import compiler.parser.InvocationExpressionPostfix
import compiler.parser.MemberAccessExpressionPostfix
import compiler.parser.NotNullExpressionPostfix
import compiler.parser.grammar.dsl.mapResult
import compiler.parser.rule.Rule

val Expression: Rule<Expression<*>> by lazy {
    sequence("expression") {
        eitherOf {
            ref(BinaryExpression)
            ref(UnaryExpression)
            ref(ValueExpression)
            ref(ParanthesisedExpression)
            ref(IfExpression)
        }
        certainty = MATCHED
        atLeast(0) {
            ref(ExpressionPostfix)
        }
        certainty = DEFINITIVE
    }
        .astTransformation { tokens ->
            val expression = tokens.next()!! as Expression<*>
            tokens
                .remainingToList()
                .fold(expression) { expr, postfix -> (postfix as ExpressionPostfix<*>).modify(expr) }
        }
}

val LiteralExpression = sequence("literal") {
    eitherOf {
        tokenOfType(TokenType.NUMERIC_LITERAL)
        // TODO: string literal, function literal
        // literals that the lexer treats as identifiers (booleans, ...?) are handled in ValueExpression
    }
    certainty = MATCHED
}
    .astTransformation { tokens ->
        when (val valueToken = tokens.next()!!) {
            is NumericLiteralToken -> NumericLiteralExpression(valueToken)
            else -> throw InternalCompilerError("Unsupported literal value $valueToken")
        }
    }

val IdentifierExpression = sequence("identifier") {
    identifier()
    certainty = DEFINITIVE
}
    .astTransformation { tokens ->
        val identifier = tokens.next() as IdentifierToken
        if (identifier.value == "true" || identifier.value == "false") {
            BooleanLiteralExpression(identifier.sourceLocation, identifier.value == "true")
        } else {
            IdentifierExpression(identifier)
        }
    }

val ValueExpression = eitherOf("value expression") {
    ref(LiteralExpression)
    ref(IdentifierExpression)
}

val ParanthesisedExpression: Rule<Expression<*>> = sequence("paranthesised expression") {
    operator(Operator.PARANT_OPEN)
    ref(Expression)
    certainty = MATCHED
    operator(Operator.PARANT_CLOSE)
    certainty = DEFINITIVE
}
    .astTransformation { tokens ->
        val parantOpen = tokens.next()!! as OperatorToken
        val nested = tokens.next()!! as Expression<*>

        ParenthesisedExpression(nested, parantOpen.sourceLocation)
    }

val UnaryExpression = sequence("unary expression") {
    eitherOf(Operator.PLUS, Operator.MINUS, Operator.NEGATE)
    // TODO: tilde, ... what else?

    eitherOf {
        // TODO: reorder these to comply to the defined operator precedence (e.g. DOT before MINUS)
        ref(ValueExpression)
        ref(ParanthesisedExpression)
    }
    certainty = DEFINITIVE
}
    .astTransformation { tokens ->
        val operator = (tokens.next()!! as OperatorToken).operator
        val expression = tokens.next()!! as Expression<*>
        UnaryExpression(operator, expression)
    }

val binaryOperators = arrayOf(
    // Arithmetic
    Operator.PLUS, Operator.MINUS, Operator.TIMES, Operator.DIVIDE,
    // Comparison
    Operator.EQUALS, Operator.GREATER_THAN, Operator.LESS_THAN, Operator.GREATER_THAN_OR_EQUALS, Operator.LESS_THAN_OR_EQUALS,
    Operator.IDENTITY_EQ, Operator.IDENTITY_NEQ,
    // MISC
    Operator.CAST, Operator.TRYCAST, Operator.ELVIS
)

val BinaryExpression = sequence("ary operator expression") {
    eitherOf {
        ref(UnaryExpression)
        ref(ValueExpression)
        ref(ParanthesisedExpression)
    }
    atLeast(1) {
        eitherOf(*binaryOperators) // TODO: arbitrary infix ops
        certainty = MATCHED
        eitherOf {
            ref(UnaryExpression)
            ref(ValueExpression)
            ref(ParanthesisedExpression)
        }
    }
    certainty = DEFINITIVE
}
    .astTransformation { tokens ->
        buildBinaryExpressionAst(tokens.remainingToList())
    }

val BracedCodeOrSingleStatement = sequence("curly braced code or single statement") {
    eitherOf {
        sequence {
            operator(Operator.CBRACE_OPEN)
            certainty = MATCHED
            optionalWhitespace()
            optional {
                ref(CodeChunk)
                certainty = DEFINITIVE
            }
            optionalWhitespace()
            operator(Operator.CBRACE_CLOSE)
            certainty = DEFINITIVE
        }
        ref(Expression)
    }
    certainty = DEFINITIVE
}
    .astTransformation { tokens ->
        var next: Any? = tokens.next()

        if (next is Executable<*>) {
            return@astTransformation next
        }

        if (next == OperatorToken(Operator.CBRACE_OPEN)) {
            throw InternalCompilerError("Unexpected $next, expecting ${Operator.CBRACE_OPEN} or executable")
        }

        next = tokens.next()

        if (next == OperatorToken(Operator.CBRACE_CLOSE)) {
            return@astTransformation CodeChunk(emptyList())
        }

        if (next !is CodeChunk) {
            throw InternalCompilerError("Unepxected $next, expecting code or ${Operator.CBRACE_CLOSE}")
        }

        return@astTransformation next
    }

val IfExpression = sequence("if-expression") {
    keyword(IF)
    certainty = MATCHED
    ref(Expression)

    ref(BracedCodeOrSingleStatement)
    certainty = OPTIMISTIC

    optionalWhitespace()

    optional {
        keyword(ELSE)
        certainty = MATCHED
        optionalWhitespace()
        ref(BracedCodeOrSingleStatement)
        certainty = DEFINITIVE
    }

    certainty = DEFINITIVE
}
    .astTransformation { tokens ->
        val ifKeyword = tokens.next() as KeywordToken

        val condition = tokens.next() as Expression<BoundExpression<Expression<*>>>
        val thenCode: Executable<*> = tokens.next() as Executable<*>
        val elseCode: Executable<*>? = if (tokens.hasNext()) {
            // skip ELSE keyword
            tokens.next()
            tokens.next() as Executable<*>
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
    certainty = DEFINITIVE
    optionalWhitespace()
}
    .astTransformation { NotNullExpressionPostfix(it.next()!! as OperatorToken) }

val ExpressionPostfixInvocation = sequence("function invocation") {
    operator(Operator.PARANT_OPEN)
    optionalWhitespace()

    optional {
        ref(Expression)
        optionalWhitespace()

        atLeast(0) {
            operator(Operator.COMMA)
            optionalWhitespace()
            ref(Expression)
        }
    }

    optionalWhitespace()
    operator(Operator.PARANT_CLOSE)
    certainty = MATCHED
}
    .astTransformation { tokens ->
        // skip PARANT_OPEN
        tokens.next()!! as OperatorToken

        val paramExpressions = mutableListOf<Expression<*>>()
        while (tokens.peek() is Expression<*>) {
            paramExpressions.add(tokens.next()!! as Expression<*>)

            // skip COMMA or PARANT_CLOSE
            tokens.next()!! as OperatorToken
        }

        InvocationExpressionPostfix(paramExpressions)
    }

val ExpressionPostfixMemberAccess = sequence("member access") {
    eitherOf(Operator.DOT, Operator.SAFEDOT)
    certainty = MATCHED
    identifier()
    certainty = OPTIMISTIC
    optionalWhitespace()
}
    .astTransformation { tokens ->
        val accessOperator = tokens.next() as OperatorToken
        val memberNameToken = tokens.next() as IdentifierToken
        MemberAccessExpressionPostfix(accessOperator, memberNameToken)
    }

val ExpressionPostfix = eitherOf {
    ref(ExpressionPostfixNotNull)
    ref(ExpressionPostfixInvocation)
    ref(ExpressionPostfixMemberAccess)
}
    .mapResult { it as ExpressionPostfix<Expression<*>> }

private typealias OperatorOrExpression = Any // kotlin does not have a union type; if it had, this would be = OperatorToken | Expression<*>

private val Operator.priority: Int
    get() = when(this) {
        Operator.ELVIS -> 10

        Operator.LESS_THAN,
        Operator.LESS_THAN_OR_EQUALS,
        Operator.GREATER_THAN,
        Operator.GREATER_THAN_OR_EQUALS,
        Operator.EQUALS,
        Operator.NOT_EQUALS,
        Operator.IDENTITY_EQ,
        Operator.IDENTITY_NEQ -> 20

        Operator.PLUS,
        Operator.MINUS -> 30

        Operator.TIMES,
        Operator.DIVIDE -> 40

        Operator.CAST,
        Operator.TRYCAST -> 60
        else -> throw InternalCompilerError("$this is not a binary operator")
    }

/**
 * Takes as input a list of alternating [Expression]s and [OperatorToken]s, e.g.:
 *     [Identifier(a), Operator(+), Identifier(b), Operator(*), Identifier(c)]
 * Builds the AST with respect to operator precedence defined in [Operator.priority]
 *
 * **Operator Precedence**
 *
 * Consider this input: `a * (b + c) + e * f + g`
 * Of those operators with the lowest precedence the rightmost will form the toplevel expression (the one
 * returned from this function). In this case it's the second `+`:
 *
 *                                   +
 *                                  / \
 *      [a, *, (b + c), +, e, *, f]    g
 *
 * This process is then recursively repeated for both sides of the node:
 *
 *                        +
 *                       / \
 *                      +   g
 *                     / \
 *     [a, *, (b + c)]    [e, *, f]
 *
 *     ---
 *               +
 *              / \
 *             +   g
 *            / \
 *           /   *
 *          /   / \
 *         *   e   f
 *        / \
 *       a  (b + c)
 */
private fun buildBinaryExpressionAst(rawExpression: List<OperatorOrExpression>): Expression<*> {
    if (rawExpression.size == 1) {
        return rawExpression[0] as? Expression<*> ?: throw InternalCompilerError("List with one item that is not an expression.. bug!")
    }

    val operatorsWithIndex = rawExpression
        .mapIndexed { index, item -> Pair(index, item) }
        .filter { it.second is OperatorToken } as List<Pair<Int, OperatorToken>>

    val rightmostWithLeastPriority = operatorsWithIndex
        .reversed()
        .minByOrNull { it.second.operator.priority }
        ?: throw InternalCompilerError("No operator in the list... how can this even be?")

    val leftOfOperator = rawExpression.subList(0, rightmostWithLeastPriority.first)
    val rightOfOperator = rawExpression.subList(rightmostWithLeastPriority.first + 1, rawExpression.size)

    return BinaryExpression(
        leftHandSide = buildBinaryExpressionAst(leftOfOperator),
        op = rightmostWithLeastPriority.second,
        rightHandSide = buildBinaryExpressionAst(rightOfOperator)
    )
}