package compiler.parser.grammar;

import compiler.lexer.Keyword.VAL
import compiler.lexer.Keyword.VAR
import compiler.lexer.Operator.*
import compiler.matching.ResultCertainty.DEFINITIVE
import compiler.matching.ResultCertainty.MATCHED
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.ModulePostProcessor
import compiler.parser.postproc.ParameterDeclarationPostProcessor
import compiler.parser.postproc.ParameterListPostprocessor

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