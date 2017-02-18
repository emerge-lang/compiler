import compiler.lexer.Keyword
import compiler.lexer.Operator.*
import compiler.parser.grammar.describeAs
import compiler.parser.grammar.postprocess
import compiler.parser.grammar.rule
import compiler.parser.postproc.FunctionPostprocessor
import compiler.parser.postproc.ImportPostprocessor
import compiler.parser.postproc.TypePostprocessor

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

val CommaSeparatedTypedParameters = rule {
    identifier()
    operator(COLON)
    __definitive()
    ref(Type)
    
    atLeast(0) {
        operator(COMMA)
        identifier()
        operator(COLON)
        __definitive()
        ref(Type)
    }
}

val TypedParameterList = rule {
    operator(PARANT_OPEN)
    
    optional {
        ref(CommaSeparatedTypedParameters)
    }
    
    operator(PARANT_CLOSE)
    __definitive()
}
    .describeAs("typed parameter list")

val FunctionDeclaration = rule {
    keyword(Keyword.FUNCTION)

    __definitive()

    optionalWhitespace()
    identifier()
    /*ref(TypedParameterList)
    optional {
        operator(RETURNS)
        identifier()
    }*/
    optionalWhitespace()
    operator(PARANT_OPEN)
    operator(PARANT_CLOSE)
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
