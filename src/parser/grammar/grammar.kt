import lexer.Keyword
import lexer.Operator.*
import parser.grammar.postprocess
import parser.grammar.rule
import parser.postproc.ImportPostprocessor

val Import = rule {
    keyword(Keyword.IMPORT)

    __definitive()

    atLeast(1) {
        identifier()
        operator(DOT)
    }
    eitherOf {
        operator(ASTERISK)
        identifier()
    }
    operator(NEWLINE)
}
.postprocess(::ImportPostprocessor)

val Type = rule {
    identifier()
    optional {
        operator(QUESTION_MARK)
    }
}

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

val FunctionDeclaration = rule {
    keyword(Keyword.FUNCTION)

    __definitive()

    identifier()
    ref(TypedParameterList)
    optional {
        operator(RETURNS)
        identifier()
    }

    operator(CBRACE_OPEN)
    operator(CBRACE_CLOSE)
}