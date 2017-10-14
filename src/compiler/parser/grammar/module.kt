package compiler.parser.grammar

import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.matching.ResultCertainty
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.ImportPostprocessor
import compiler.parser.postproc.ModuleDeclarationPostProcessor

val ModuleDeclaration = sequence {
    keyword(Keyword.MODULE)

    certainty = ResultCertainty.MATCHED

    identifier()

    certainty = ResultCertainty.OPTIMISTIC

    atLeast(0) {
        operator(Operator.DOT)
        certainty = ResultCertainty.MATCHED
        identifier()
    }
    operator(Operator.NEWLINE)
}
    .describeAs("module declaration")
    .postprocess(::ModuleDeclarationPostProcessor)

val ImportDeclaration = sequence {
    keyword(Keyword.IMPORT)

    certainty = ResultCertainty.MATCHED

    atLeast(1) {
        identifier()
        operator(Operator.DOT)
    }
    certainty = ResultCertainty.OPTIMISTIC
    identifier(acceptedOperators = listOf(Operator.TIMES))
    operator(Operator.NEWLINE)
}
    .describeAs("import declaration")
    .postprocess(::ImportPostprocessor)