package compiler.parser.grammar

import VariableDeclaration
import compiler.ast.CodeChunk
import compiler.lexer.Keyword
import compiler.lexer.Operator
import compiler.matching.ResultCertainty.*
import compiler.parser.TokenSequence
import compiler.parser.grammar.dsl.describeAs
import compiler.parser.grammar.dsl.eitherOf
import compiler.parser.grammar.dsl.postprocess
import compiler.parser.grammar.dsl.sequence
import compiler.parser.postproc.*
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult

class CodeChunkRule : Rule<CodeChunk> {
    override val descriptionOfAMatchingThing = "code"

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<CodeChunk> {
        return rule.tryMatch(input)
    }

    private val rule by lazy {
        val oneLine = eitherOf {
            ref(VariableDeclaration)
            ref(AssignmentStatement)
            ref(ReturnStatement)
            expression()
        }

        sequence {
            certainty = MATCHED
            optional {
                ref(oneLine)

                atLeast(0) {
                    atLeast(0) {
                        operator(Operator.NEWLINE)
                        certainty = MATCHED
                    }

                    ref(oneLine)
                    certainty = DEFINITIVE
                }
                certainty = DEFINITIVE
            }

            certainty = OPTIMISTIC
        }
            .postprocess(::CodeChunkPostProcessor)
    }

    companion object {
        val INSTANCE = CodeChunkRule()
    }
}

val ReturnStatement = sequence {
    keyword(Keyword.RETURN)
    certainty = MATCHED
    expression()
    certainty = DEFINITIVE
}
    .describeAs("return statement")
    .postprocess(::ReturnStatementPostProcessor)

val AssignmentStatement = sequence {
    expression()

    operator(Operator.ASSIGNMENT)
    certainty = MATCHED

    expression()
    certainty = DEFINITIVE
}
    .describeAs("assignment")
    .flatten()
    .mapResult(::toAST_AssignmentStatement)