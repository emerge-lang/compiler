import compiler.lexer.Keyword
import compiler.lexer.Operator.*
import compiler.parser.grammar.describeAs
import compiler.parser.grammar.postprocess
import compiler.parser.grammar.rule
import compiler.parser.postproc.*

val ImportDeclaration = rule {
    keyword(Keyword.IMPORT)

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

val Type = rule {
    identifier()
    optional {
        operator(QUESTION_MARK)
    }
}
    .describeAs("type")
    .postprocess(::TypePostprocessor)

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
    keyword(Keyword.FUNCTION)

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
