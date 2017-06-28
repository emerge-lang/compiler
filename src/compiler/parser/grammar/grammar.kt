import compiler.lexer.Keyword.*
import compiler.lexer.Operator.*
import compiler.parser.grammar.*
import compiler.parser.postproc.*

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