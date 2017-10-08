package compiler.parser.grammar.dsl

import compiler.lexer.Keyword
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.matching.ResultCertainty
import compiler.parser.TokenSequence
import compiler.parser.rule.Rule
import compiler.parser.toTransactional

typealias Grammar = GrammarReceiver.() -> Any?
typealias SequenceGrammar = SequenceRuleDefinitionReceiver.() -> Any?

class SequenceGrammarRule(private val grammar: SequenceGrammar): Rule<List<*>> {
    override val descriptionOfAMatchingThing by lazy { describeSequenceGrammar(grammar) }
    override fun tryMatch(input: TokenSequence) = tryMatchSequence(grammar, input)
}

fun sequence(matcherFn: SequenceGrammar) = SequenceGrammarRule(matcherFn)

fun eitherOf(mismatchCertainty: ResultCertainty, matcherFn: Grammar): Rule<*> {
    return object : Rule<Any?> {
        override val descriptionOfAMatchingThing = describeEitherOfGrammar(matcherFn)
        override fun tryMatch(input: TokenSequence) = tryMatchEitherOf(matcherFn, input, mismatchCertainty)
    }
}

fun eitherOf(matcherFn: Grammar) = eitherOf(ResultCertainty.NOT_RECOGNIZED, matcherFn)

fun main(args: Array<String>) {
    val code = "import val fun import import import"
    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = code.split("\n")
    }
    val input = lex(code, source).toTransactional(source.toLocation(1, 1))
    val rule = sequence {
        sequence {
            keyword(Keyword.IMPORT)
            keyword(Keyword.VAL)
            keyword(Keyword.FUNCTION)
        }
        atLeast(2) {
            keyword(Keyword.IMPORT)
        }
    }
    val result = rule.tryMatch(input)
    println("Done")
}