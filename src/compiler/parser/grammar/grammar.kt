import compiler.lexer.Keyword.*
import compiler.lexer.Operator.*
import compiler.matching.ResultCertainty.*
import compiler.parser.grammar.CodeChunk
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.*

val ModuleDeclaration = sequence {
    keyword(MODULE)

    certainty = MATCHED

    identifier()

    certainty = OPTIMISTIC

    atLeast(0) {
        operator(DOT)
        identifier()
    }
    operator(NEWLINE)
}
    .describeAs("module declaration")
    .postprocess(::ModuleDeclarationPostProcessor)

val ImportDeclaration = sequence {
    keyword(IMPORT)

    certainty = MATCHED

    atLeast(1) {
        identifier()
        operator(DOT)
    }
    certainty = OPTIMISTIC
    identifier(acceptedOperators = listOf(TIMES))
    operator(NEWLINE)
}
    .describeAs("import declaration")
    .postprocess(::ImportPostprocessor)

val TypeModifier = sequence {
    eitherOf {
        keyword(MUTABLE)
        keyword(READONLY)
        keyword(IMMUTABLE)
    }
    certainty = DEFINITIVE
}
    .describeAs("type modifier")
    .postprocess(::TypeModifierPostProcessor)

val Type = sequence {
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

val VariableDeclaration = sequence {

    optional {
        ref(TypeModifier)
    }

    optionalWhitespace()

    eitherOf {
        keyword(VAR)
        keyword(VAL)
    }
    certainty = MATCHED

    optionalWhitespace()

    identifier()
    certainty = OPTIMISTIC

    optional {
        operator(COLON)
        ref(Type)
    }

    optional {
        optionalWhitespace()
        operator(ASSIGNMENT)
        certainty = DEFINITIVE
        expression()
    }

    certainty = DEFINITIVE
}
    .describeAs("variable declaration")
    .postprocess(::VariableDeclarationPostProcessor)

val Parameter = sequence {

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

val ParameterList = sequence {
    operator(PARANT_OPEN)

    optionalWhitespace()

    optional {
        ref(Parameter)

        optionalWhitespace()

        atLeast(0) {
            operator(COMMA)
            optionalWhitespace()
            ref(Parameter)
        }
    }

    optionalWhitespace()
    operator(PARANT_CLOSE)
}
    .describeAs("parenthesised paramete rlist")
    .postprocess(::ParameterListPostprocessor)

val FunctionModifier = sequence {
    eitherOf {
        keyword(READONLY)
        keyword(NOTHROW)
        keyword(PURE)
        keyword(OPERATOR)
        keyword(EXTERNAL)
    }
    certainty = DEFINITIVE
}
    .postprocess(::FunctionModifierPostProcessor)

val StandaloneFunctionDeclaration = sequence {
    atLeast(0) {
        ref(FunctionModifier)
    }

    keyword(FUNCTION)

    certainty = MATCHED

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

    certainty = OPTIMISTIC

    eitherOf {
        sequence {
            optionalWhitespace()
            operator(CBRACE_OPEN)
            certainty = DEFINITIVE
            ref(CodeChunk)
            optionalWhitespace()
            operator(CBRACE_CLOSE)
        }
        sequence {
            operator(ASSIGNMENT)
            certainty = DEFINITIVE
            expression()
            eitherOf {
                operator(NEWLINE)
                endOfInput()
            }
        }
        operator(NEWLINE)
        endOfInput()
    }

    certainty = DEFINITIVE
}
    .describeAs("function declaration")
    .postprocess(::StandaloneFunctionPostprocessor)

val Module = sequence {
    certainty = MATCHED
    atLeast(0) {
        optionalWhitespace()
        eitherOf(mismatchCertainty = DEFINITIVE) {
            ref(ModuleDeclaration)
            ref(ImportDeclaration)
            ref(VariableDeclaration)
            ref(StandaloneFunctionDeclaration)
            endOfInput()
        }
        certainty = DEFINITIVE
    }
}
    .describeAs("module")
    .postprocess(::ModulePostProcessor)