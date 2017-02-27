import compiler.ast.ModuleDeclaration
import compiler.ast.context.Module
import compiler.ast.expression.Expression
import compiler.lexer.Keyword.*
import compiler.lexer.Operator.*
import compiler.lexer.TokenType
import compiler.parser.grammar.*
import compiler.parser.postproc.*
import compiler.parser.rule.Rule

val ModuleDeclaration = rule {
    keyword(MODULE)

    __definitive()

    identifier()

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

    __definitive()

    atLeast(1) {
        identifier()
        operator(DOT)
    }
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
    __definitive()
    optional {
        operator(NOTNULL)
    }
}
    .describeAs("literal")
    .postprocess(::LiteralExpressionPostProcessor)

val ValueExpression = rule {
    eitherOf {
        ref(LiteralExpression)
        identifier()
    }
    optional {
        operator(NOTNULL)
    }
    __definitive()
}
    .describeAs("value expression")
    .postprocess(::ValueExpressionPostProcessor)

val ParanthesisedExpression: Rule<Expression> = rule {
    operator(PARANT_OPEN)
    expression()
    __definitive()
    operator(PARANT_CLOSE)
}
    .describeAs("paranthesised expression")
    .postprocess(::ParanthesisedExpressionPostProcessor)

val UnaryExpression = rule {
    eitherOf(PLUS, MINUS, NEGATE)
    // TODO: tilde, ... what else?

    eitherOf {
        ref(ValueExpression)
        ref(ParanthesisedExpression)
    }
    __definitive()
}
    .describeAs("unary expression")
    .postprocess(::UnaryExpressionPostProcessor)

val aryOperators = arrayOf(
    // Object access
    DOT, SAFEDOT,
    // Arithmetic
    PLUS, MINUS, TIMES, DIVIDE,
    // Comparison
    EQUALS, GREATER_THAN, LESS_THAN, GREATER_THAN_OR_EQUALS, LESS_THAN_OR_EQUALS,
    IDENTITY_EQ, IDENTITY_NEQ,
    // MISC
    CAST, TRYCAST, ELVIS
)
val AryExpression: Rule<Expression> = rule {
    eitherOf {
        ref(UnaryExpression)
        ref(ValueExpression)
        ref(ParanthesisedExpression)
    }
    eitherOf(*aryOperators) // TODO: more ary ops, arbitrary infix ops
    __definitive()
    expression()
}
    .describeAs("ary operator expression")
    .postprocess(::AryExpressionPostProcessor)

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

    operator(ASSIGNMENT)
    expression()
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

val ModuleMatcher: (ModuleDeclaration) -> Rule<Module> = {
    defaultDeclaration ->
    ModulePostProcessor(
        rule {
            atLeast(0) {
                optionalWhitespace()
                eitherOf {
                    ref(ModuleDeclaration)
                    ref(ImportDeclaration)
                    ref(VariableDeclaration)
                    ref(FunctionDeclaration)
                }
                optionalWhitespace()
            }
        }
        .describeAs("module")
    )(defaultDeclaration)
}