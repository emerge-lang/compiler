package compiler.parser.grammar

import compiler.ast.expression.Expression
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.ELSE
import compiler.lexer.Keyword.IF
import compiler.lexer.Operator
import compiler.lexer.OperatorToken
import compiler.lexer.TokenType
import compiler.matching.ResultCertainty.*
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.*
import compiler.parser.rule.Rule

val Expression: Rule<Expression<*>> by lazy {
    sequence {
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
        .postprocess(::ExpressionPostprocessor)
}

val LiteralExpression = sequence {
    eitherOf {
        tokenOfType(TokenType.NUMERIC_LITERAL)
        // TODO: string literal, function literal
        // literals that the lexer treats as identifiers (booleans, ...?) are handled in ValueExpression
    }
    certainty = MATCHED
}
    .describeAs("literal")
    .postprocess(::LiteralExpressionPostProcessor)

val ValueExpression = sequence {
    eitherOf {
        ref(LiteralExpression)
        identifier()
    }
    certainty = DEFINITIVE
}
    .describeAs("value expression")
    .postprocess(::ValueExpressionPostProcessor)

val ParanthesisedExpression: Rule<Expression<*>> = sequence {
    operator(Operator.PARANT_OPEN)
    ref(Expression)
    certainty = MATCHED
    operator(Operator.PARANT_CLOSE)
    certainty = DEFINITIVE
}
    .describeAs("paranthesised expression")
    .postprocess(::ParanthesisedExpressionPostProcessor)

val UnaryExpression = sequence {
    eitherOf(Operator.PLUS, Operator.MINUS, Operator.NEGATE)
    // TODO: tilde, ... what else?

    eitherOf {
        // TODO: reorder these to comply to the defined operator precedence (e.g. DOT before MINUS)
        ref(ValueExpression)
        ref(ParanthesisedExpression)
    }
    certainty = DEFINITIVE
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

val BinaryExpression = sequence {
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
    .describeAs("ary operator expression")
    .postprocess(::BinaryExpressionPostProcessor)

val BracedCodeOrSingleStatement = sequence {
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
    .describeAs("curly braced code or single statement")
    .postprocess(::BracedCodeOrSingleStatementPostProcessor)

val IfExpression = sequence {
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
    .describeAs("if-expression")
    .postprocess(::IfExpressionPostProcessor)

val ExpressionPostfixNotNull = sequence {
    operator(Operator.NOTNULL)
    certainty = DEFINITIVE
    optionalWhitespace()
}
    .describeAs(OperatorToken(Operator.NOTNULL).toStringWithoutLocation())
    .flatten()
    .mapResult { NotNullExpressionPostfixModifier(it.next()!! as OperatorToken) }

val ExpressionPostfixInvocation = sequence {
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
    .describeAs("function invocation")
    .flatten()
    .mapResult(InvocationExpressionPostfixModifier.Companion::fromMatchedTokens)

val ExpressionPostfixMemberAccess = sequence {
    eitherOf(Operator.DOT, Operator.SAFEDOT)
    certainty = MATCHED
    identifier()
    certainty = OPTIMISTIC
    optionalWhitespace()
}
    .describeAs("member access")
    .flatten()
    .mapResult {
        val accessOperator = it.next() as OperatorToken
        val memberNameToken = it.next() as IdentifierToken
        MemberAccessExpressionPostfixModifier(accessOperator, memberNameToken)
    }

val ExpressionPostfix = sequence {
    eitherOf {
        ref(ExpressionPostfixNotNull)
        ref(ExpressionPostfixInvocation)
        ref(ExpressionPostfixMemberAccess)
    }
    certainty = OPTIMISTIC
}
    .flatten()
    .mapResult { it.next()!! as ExpressionPostfixModifier<Expression<*>> }