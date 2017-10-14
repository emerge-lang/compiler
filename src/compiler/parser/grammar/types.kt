package compiler.parser.grammar

import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.matching.ResultCertainty
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.TypeModifierPostProcessor
import compiler.parser.postproc.TypePostprocessor

val TypeModifier = sequence {
    eitherOf {
        keyword(Keyword.MUTABLE)
        keyword(Keyword.READONLY)
        keyword(Keyword.IMMUTABLE)
    }
    certainty = ResultCertainty.DEFINITIVE
}
    .describeAs("type modifier")
    .postprocess(::TypeModifierPostProcessor)

val Type = sequence {
    optional {
        ref(TypeModifier)
    }

    identifier()
    optional {
        operator(Operator.QUESTION_MARK)
    }

    // TODO: function types
    // TODO: generics
}
    .describeAs("type")
    .postprocess(::TypePostprocessor)