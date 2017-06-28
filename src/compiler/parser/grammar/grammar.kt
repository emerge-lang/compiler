import compiler.ast.expression.Expression
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword.*
import compiler.lexer.Operator
import compiler.lexer.Operator.*
import compiler.lexer.OperatorToken
import compiler.lexer.TokenType
import compiler.parser.grammar.describeAs
import compiler.parser.grammar.postprocess
import compiler.parser.grammar.rule
import compiler.parser.postproc.*
import compiler.parser.rule.Rule

val ModuleDeclaration = rule {
    keyword(MODULE)

    __matched()

    identifier()

    __optimistic()

    atLeast(0) {
        operator(DOT)
        identifier()
    }
    operator(NEWLINE)
}
    .describeAs("module declaration")
    .postprocess(::ModuleDeclarationPostProcessor)

val ImportDeclaration = rule {
    keyword(IMPORT)

    __matched()

    atLeast(1) {
        identifier()
        operator(DOT)
    }
    __optimistic()
    identifier(acceptedOperators = listOf(TIMES))
    operator(NEWLINE)
}
    .describeAs("import declaration")
    .postprocess(::ImportPostprocessor)

val TypeModifier = rule {
    eitherOf {
        keyword(MUTABLE)
        keyword(READONLY)
        keyword(IMMUTABLE)
    }
    __definitive()
}
    .describeAs("type modifier")
    .postprocess(::TypeModifierPostProcessor)

val Type = rule {
    optional {
        ref(TypeModifier)
    }

    identifier()
    optional {
        operator(QUESTION_MARK)
    }
}
    .describeAs("type")
    .postprocess(::TypePostprocessor)

val LiteralExpression = rule {
    eitherOf {
        tokenOfType(TokenType.NUMERIC_LITERAL)
        // TODO: string literal, function literal
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
    operator(PARANT_OPEN)
    expression()
    __matched()
    operator(PARANT_CLOSE)
    __definitive()
}
    .describeAs("paranthesised expression")
    .postprocess(::ParanthesisedExpressionPostProcessor)

val UnaryExpression = rule {
    eitherOf(PLUS, MINUS, NEGATE)
    // TODO: tilde, ... what else?

    eitherOf { // TODO: reorder these to comply to the defined operator precedence (e.g. DOT before MINUS)
        ref(ValueExpression)
        ref(ParanthesisedExpression)
    }
    __definitive()
}
    .describeAs("unary expression")
    .postprocess(::UnaryExpressionPostProcessor)

val binaryOperators = arrayOf(
    // Arithmetic
    PLUS, MINUS, TIMES, DIVIDE,
    // Comparison
    EQUALS, GREATER_THAN, LESS_THAN, GREATER_THAN_OR_EQUALS, LESS_THAN_OR_EQUALS,
    IDENTITY_EQ, IDENTITY_NEQ,
    // MISC
    CAST, TRYCAST, ELVIS
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

val ExpressionPostfixNotNull = rule {
    operator(NOTNULL)
    __definitive()
}
    .describeAs(OperatorToken(NOTNULL).toStringWithoutLocation())
    .flatten()
    .mapResult { NotNullExpressionPostfixModifier(it.next()!! as OperatorToken) }

val ExpressionPostfixInvocation = rule {
    operator(PARANT_OPEN)
    optionalWhitespace()

    optional {
        expression()
        optionalWhitespace()

        atLeast(0) {
            operator(COMMA)
            optionalWhitespace()
            expression()
        }
    }

    optionalWhitespace()
    operator(PARANT_CLOSE)
    __matched()
}
    .describeAs("function invocation")
    .flatten()
    .mapResult(InvocationExpressionPostfixModifier.Companion::fromMatchedTokens)

val ExpressionPostfixMemberAccess = rule {
    eitherOf(DOT, SAFEDOT)
    __matched()
    identifier()
    __optimistic()
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

val VariableDeclaration = rule {

    optional {
        ref(TypeModifier)
    }

    optionalWhitespace()

    eitherOf {
        keyword(VAR)
        keyword(VAL)
    }
    __matched()

    optionalWhitespace()

    identifier()
    __optimistic()

    optional {
        operator(COLON)
        ref(Type)
    }

    optional {
        optionalWhitespace()
        operator(ASSIGNMENT)
        __definitive()
        expression()
    }

    eitherOf {
        operator(NEWLINE)
        endOfInput()
    }
    __definitive()
}
    .describeAs("variable declaration")
    .postprocess(::VariableDeclarationPostProcessor)

val Parameter = rule {

    optional {
        ref(TypeModifier)
    }

    optional {
        eitherOf {
            keyword(VAR)
            keyword(VAL)
        }
    }

    identifier()

    optional {
        operator(COLON)
        ref(Type)
    }
}
    .describeAs("parameter declaration")
    .postprocess(::ParameterDeclarationPostProcessor)

val ParameterList = rule {
    operator(PARANT_OPEN)

    optionalWhitespace()

    optional {
        ref(rule { // TODO: remove the ref(rule { ??
            ref(Parameter)

            optionalWhitespace()

            atLeast(0) {
                operator(COMMA)
                optionalWhitespace()
                ref(Parameter)
            }
        })
    }

    optionalWhitespace()
    operator(PARANT_CLOSE)
}
    .describeAs("parenthesised paramete rlist")
    .postprocess(::ParameterListPostprocessor)

val FunctionModifier = rule {
    eitherOf {
        keyword(READONLY)
        keyword(NOTHROW)
        keyword(PURE)
        keyword(OPERATOR)
        keyword(EXTERNAL)
    }
    __definitive()
}
    .postprocess(::FunctionModifierPostProcessor)

val StandaloneFunctionDeclaration = rule {
    atLeast(0) {
        ref(FunctionModifier)
    }

    keyword(FUNCTION)

    __matched()

    optional {
        ref(Type)
        operator(DOT)
    }

    optionalWhitespace()
    identifier()
    optionalWhitespace()
    ref(ParameterList)
    optionalWhitespace()

    optional {
        operator(RETURNS)
        optionalWhitespace()
        ref(Type)
    }

    __optimistic()

    eitherOf {
        sequence {
            optionalWhitespace()
            operator(CBRACE_OPEN)
            __definitive()
            codeChunk()
            operator(CBRACE_CLOSE)
        }
        eitherOf {
            operator(NEWLINE)
            endOfInput()
        }
    }

    __definitive()
}
    .describeAs("function declaration")
    .postprocess(::StandaloneFunctionPostprocessor)

val Module = rule {
    atLeast(0) {
        __definitive()
        optionalWhitespace()
        eitherOf {
            ref(ModuleDeclaration)
            ref(ImportDeclaration)
            ref(VariableDeclaration)
            ref(StandaloneFunctionDeclaration)
        }
        optionalWhitespace()
    }
}
    .describeAs("module")
    .postprocess(::ModulePostProcessor)