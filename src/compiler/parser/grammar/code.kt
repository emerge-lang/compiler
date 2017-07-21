package compiler.parser.grammar

import VariableDeclaration
import compiler.ast.CodeChunk
import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.parser.TokenSequence
import compiler.parser.postproc.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult

class CodeChunkRule : Rule<CodeChunk> {
    override val descriptionOfAMatchingThing = "code"

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<CodeChunk> {
        return rule.tryMatch(input)
    }

    private val rule by lazy {
        rule {
            __matched()
            atLeast(0) {
                optionalWhitespace()
                eitherOf {
                    ref(VariableDeclaration)
                    ref(AssignmentStatement)
                    ref(ReturnStatement)
                    expression()
                }
                __optimistic()
            }
            __optimistic()
        }
            .postprocess(::CodeChunkPostProcessor)
    }

    companion object {
        val INSTANCE = CodeChunkRule()
    }
}

val ReturnStatement = rule {
    keyword(Keyword.RETURN)
    __matched()
    expression()
    __definitive()
}
    .describeAs("return statement")
    .postprocess(::ReturnStatementPostProcessor)

val AssignmentStatement = rule {
    expression()

    operator(Operator.ASSIGNMENT)
    __matched()

    expression()
    __optimistic()

    eitherOf {
        operator(Operator.NEWLINE)
        endOfInput()
    }
    __definitive()
}
    .describeAs("assignment")
    .flatten()
    .mapResult(::toAST_AssignmentStatement)