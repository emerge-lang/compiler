package compiler.parser.grammar

import ReturnStatement
import VariableDeclaration
import compiler.ast.CodeChunk
import compiler.lexer.Operator
import compiler.parser.TokenSequence
import compiler.parser.postproc.CodeChunkPostProcessor
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult

class CodeChunkRule : Rule<CodeChunk> {
    override val descriptionOfAMatchingThing = "code"

    override fun tryMatch(input: TokenSequence): RuleMatchingResult<CodeChunk> {
        return rule.tryMatch(input)
    }

    private val rule by lazy {
        rule {
            atLeast(0) {
                optionalWhitespace()
                eitherOf {
                    ref(VariableDeclaration)
                    ref(ReturnStatement)
                    expression()
                }
                __matched()
                eitherOf {
                    operator(Operator.NEWLINE)
                    endOfInput()
                    optionalWhitespace()
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