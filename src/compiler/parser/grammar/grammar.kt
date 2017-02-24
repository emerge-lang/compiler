import compiler.ast.expression.Expression
import compiler.lexer.Keyword.*
import compiler.lexer.Operator.*
import compiler.lexer.TokenType
import compiler.lexer.TokenType.*
import compiler.parser.grammar.*
import compiler.parser.postproc.*
import compiler.parser.rule.Rule

val ImportDeclaration = rule {
    keyword(IMPORT)

    __definitive()

    atLeast(1) {
        identifier()
        operator(DOT)
    }
    identifier(acceptedOperators = listOf(ASTERISK))
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
        // TODO: string literal, function literal, and so forth
    }
}
    .describeAs("literal")
    .postprocess(::LiteralExpressionPostProcessor)

val ValueExpression = rule {
    eitherOf {
        ref(LiteralExpression)
        identifier()
    }
}
    .describeAs("value expression")
    .postprocess(::ValueExpressionPostProcessor)

val ParanthesisedExpression: Rule<Expression> = rule {
    operator(PARANT_OPEN)
    ref(ExpressionRule.INSTANCE)
    __definitive()
    operator(PARANT_CLOSE)
}
    .postprocess(::ParanthesisedExpressionPostProcessor)

val UnaryExpression = rule {
    eitherOf {
        operator(PLUS)
        operator(MINUS)
        operator(NEGATE)
        // TODO: tilde, ... what else?
    }
    ref(ExpressionRule.INSTANCE)
    __definitive()
}

val VariableDeclaration = rule {

    optional {
        ref(TypeModifier)
    }

    optionalWhitespace()

    eitherOf {
        keyword(VAR)
        keyword(VAL)
    }
    __definitive()

    optionalWhitespace()

    identifier()

    optional {
        operator(COLON)
        ref(Type)
    }

    optionalWhitespace()

    operator(EQUALS)

    ref(ExpressionRule.INSTANCE)
    operator(NEWLINE)
}
    .describeAs("variable declaration")
    .postprocess(::VariableDeclarationPostProcessor)

val Parameter = rule {
    identifier()

    optional {
        operator(COLON)
        __definitive()
        ref(Type)
    }
}
    .postprocess(::ParameterPostprocessor)

val ParameterList = rule {
    operator(PARANT_OPEN)

    optionalWhitespace()

    optional {
        ref(rule {
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

val FunctionDeclaration = rule {
    keyword(FUNCTION)

    __definitive()

    optionalWhitespace()
    identifier()
    optionalWhitespace()
    ref(ParameterList)
    optionalWhitespace()

    optional {
        operator(RETURNS)
        optionalWhitespace()
        ref(Type)
        optionalWhitespace()
    }

    operator(CBRACE_OPEN)
    optionalWhitespace()
    operator(CBRACE_CLOSE)
}
    .describeAs("function declaration")
    .postprocess(::FunctionPostprocessor)
