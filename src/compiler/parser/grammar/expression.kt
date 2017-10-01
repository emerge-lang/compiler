package compiler.parser.grammar

import compiler.ast.expression.Expression
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.ELSE
import compiler.lexer.Keyword.IF
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.TokenType
import compiler.parser.TokenSequence
import compiler.parser.postproc.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.transact.Position
import compiler.transact.TransactionalSequence

class ExpressionRule : Rule<Expression<*>> {
    override val descriptionOfAMatchingThing = "expression"

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<Expression<*>> {
        return rule.tryMatch(input)
    }

    private val rule by lazy {
        rule {
            eitherOf {
                ref(BinaryExpression)
                ref(UnaryExpression)
                ref(ValueExpression)
                ref(ParanthesisedExpression)
                ref(IfExpression)
            }
            __matched()
            atLeast(0) {
                ref(ExpressionPostfix)
            }
            __definitive()
        }
            .flatten()
            .mapResult(this::postprocess)
    }

    private fun postprocess(input: TransactionalSequence<Any, Position>): Expression<*> {
        var expression = input.next()!! as Expression<*>
        @Suppress("UNCHECKED_CAST")
        val postfixes = input.remainingToList() as List<ExpressionPostfixModifier<*>>

        for (postfixMod in postfixes) {
            expression = postfixMod.modify(expression)
        }

        return expression
    }

    companion object {
        val INSTANCE = ExpressionRule()
    }
}

val LiteralExpression = rule {
    eitherOf {
        tokenOfType(TokenType.NUMERIC_LITERAL)
        // TODO: string literal, function literal
        // literals that the lexer treats as identifiers (booleans, ...?) are handled in ValueExpression
    }
    __matched()
}
    .describeAs("literal")
    .postprocess(::LiteralExpressionPostProcessor)

val ValueExpression = rule {
    eitherOf {
        ref(LiteralExpression)
        identifier()
    }
    __definitive()
}
    .describeAs("value expression")
    .postprocess(::ValueExpressionPostProcessor)

val ParanthesisedExpression: Rule<Expression<*>> = rule {
    operator(Operator.PARANT_OPEN)
    expression()
    __matched()
    operator(Operator.PARANT_CLOSE)
    __definitive()
}
    .describeAs("paranthesised expression")
    .postprocess(::ParanthesisedExpressionPostProcessor)

val UnaryExpression = rule {
    eitherOf(Operator.PLUS, Operator.MINUS, Operator.NEGATE)
    // TODO: tilde, ... what else?

    eitherOf {
        // TODO: reorder these to comply to the defined operator precedence (e.g. DOT before MINUS)
        ref(ValueExpression)
        ref(ParanthesisedExpression)
    }
    __definitive()
}
    .describeAs("unary expression")
    .postprocess(::UnaryExpressionPostProcessor)

val binaryOperators = arrayOf(
    // Arithmetic
    Operator.PLUS, Operator.MINUS, Operator.TIMES, Operator.DIVIDE,
    // Comparison
    Operator.EQUALS, Operator.GREATER_THAN, Operator.LESS_THAN, Operator.GREATER_THAN_OR_EQUALS, Operator.LESS_THAN_OR_EQUALS,
    Operator.IDENTITY_EQ, Operator.IDENTITY_NEQ,
    // MISC
    Operator.CAST, Operator.TRYCAST, Operator.ELVIS
)

val BinaryExpression = rule {
    eitherOf {
        ref(UnaryExpression)
        ref(ValueExpression)
        ref(ParanthesisedExpression)
    }
    atLeast(1) {
        eitherOf(*binaryOperators) // TODO: arbitrary infix ops
        __matched()
        eitherOf {
            ref(UnaryExpression)
            ref(ValueExpression)
            ref(ParanthesisedExpression)
        }
    }
    __definitive()
}
    .describeAs("ary operator expression")
    .postprocess(::BinaryExpressionPostProcessor)

val BracedCodeOrSingleStatement = rule {
    eitherOf {
        sequence {
            operator(Operator.CBRACE_OPEN)
            __matched()
            optionalWhitespace()
            optional {
                codeChunk()
                __definitive()
            }
            optionalWhitespace()
            operator(Operator.CBRACE_CLOSE)
            __definitive()
        }
        expression()
    }
    __definitive()
}
    .describeAs("curly braced code or single statement")
    .postprocess(::BracedCodeOrSingleStatementPostProcessor)

val IfExpression = rule {
    keyword(IF)
    __matched()
    expression()

    ref(BracedCodeOrSingleStatement)
    __optimistic()

    optionalWhitespace()

    optional {
        keyword(ELSE)
        __matched()
        optionalWhitespace()
        ref(BracedCodeOrSingleStatement)
        __definitive()
    }

    __definitive()
}
    .describeAs("if-expression")
    .postprocess(::IfExpressionPostProcessor)

val ExpressionPostfixNotNull = rule {
    operator(Operator.NOTNULL)
    __definitive()
    optionalWhitespace()
}
    .describeAs(OperatorToken(Operator.NOTNULL).toStringWithoutLocation())
    .flatten()
    .mapResult { NotNullExpressionPostfixModifier(it.next()!! as OperatorToken) }

val ExpressionPostfixInvocation = rule {
    operator(Operator.PARANT_OPEN)
    optionalWhitespace()

    optional {
        expression()
        optionalWhitespace()

        atLeast(0) {
            operator(Operator.COMMA)
            optionalWhitespace()
            expression()
        }
    }

    optionalWhitespace()
    operator(Operator.PARANT_CLOSE)
    __matched()
    optionalWhitespace()
}
    .describeAs("function invocation")
    .flatten()
    .mapResult(InvocationExpressionPostfixModifier.Companion::fromMatchedTokens)

val ExpressionPostfixMemberAccess = rule {
    eitherOf(Operator.DOT, Operator.SAFEDOT)
    __matched()
    identifier()
    __optimistic()
    optionalWhitespace()
}
    .describeAs("member access")
    .flatten()
    .mapResult {
        val accessOperator = it.next() as OperatorToken
        val memberNameToken = it.next() as IdentifierToken
        MemberAccessExpressionPostfixModifier(accessOperator, memberNameToken)
    }

val ExpressionPostfix = rule {
    eitherOf {
        ref(ExpressionPostfixNotNull)
        ref(ExpressionPostfixInvocation)
        ref(ExpressionPostfixMemberAccess)
    }
    __optimistic()
}
    .flatten()
    .mapResult { it.next()!! as ExpressionPostfixModifier<Expression<*>> }