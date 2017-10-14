package compiler.parser.grammar

import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.matching.ResultCertainty
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.FunctionModifierPostProcessor
import compiler.parser.postproc.StandaloneFunctionPostprocessor
import compiler.parser.postproc.VariableDeclarationPostProcessor

val VariableDeclaration = sequence {

    optional {
        ref(TypeModifier)
    }

    optionalWhitespace()

    eitherOf {
        keyword(Keyword.VAR)
        keyword(Keyword.VAL)
    }
    certainty = ResultCertainty.MATCHED

    optionalWhitespace()

    identifier()
    certainty = ResultCertainty.OPTIMISTIC

    optional {
        operator(Operator.COLON)
        ref(Type)
    }

    optional {
        optionalWhitespace()
        operator(Operator.ASSIGNMENT)
        certainty = ResultCertainty.DEFINITIVE
        ref(Expression)
    }

    certainty = ResultCertainty.DEFINITIVE
}
    .describeAs("variable declaration")
    .postprocess(::VariableDeclarationPostProcessor)

val FunctionModifier = sequence {
    eitherOf {
        keyword(Keyword.READONLY)
        keyword(Keyword.NOTHROW)
        keyword(Keyword.PURE)
        keyword(Keyword.OPERATOR)
        keyword(Keyword.EXTERNAL)
    }
    certainty = ResultCertainty.DEFINITIVE
}
    .postprocess(::FunctionModifierPostProcessor)

val StandaloneFunctionDeclaration = sequence {
    atLeast(0) {
        ref(FunctionModifier)
    }

    keyword(Keyword.FUNCTION)

    certainty = ResultCertainty.MATCHED

    optional {
        ref(Type)
        operator(Operator.DOT)
    }

    optionalWhitespace()
    identifier()
    optionalWhitespace()
    ref(ParameterList)
    optionalWhitespace()

    optional {
        operator(Operator.RETURNS)
        optionalWhitespace()
        ref(Type)
    }

    certainty = ResultCertainty.OPTIMISTIC

    eitherOf {
        sequence {
            optionalWhitespace()
            operator(Operator.CBRACE_OPEN)
            certainty = ResultCertainty.DEFINITIVE
            ref(CodeChunk)
            optionalWhitespace()
            operator(Operator.CBRACE_CLOSE)
        }
        sequence {
            operator(Operator.ASSIGNMENT)
            certainty = ResultCertainty.DEFINITIVE
            ref(Expression)
            eitherOf {
                operator(Operator.NEWLINE)
                endOfInput()
            }
        }
        operator(Operator.NEWLINE)
        endOfInput()
    }

    certainty = ResultCertainty.DEFINITIVE
}
    .describeAs("function declaration")
    .postprocess(::StandaloneFunctionPostprocessor)