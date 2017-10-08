package compiler.parser.grammar.dsl

import compiler.lexer.Keyword
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.parser.TokenSequence
import compiler.parser.rule.Rule
import compiler.parser.rule.RuleMatchingResult
import compiler.parser.toTransactional

typealias Grammar = GrammarReceiver.() -> Any?
typealias SequenceGrammar = SequenceRuleDefinitionReceiver.() -> Any?

fun sequence(matcherFn: SequenceGrammar): Rule<List<RuleMatchingResult<*>>> {
    return object : Rule<List<RuleMatchingResult<*>>> {
        override val descriptionOfAMatchingThing = describeSequenceGrammar(matcherFn)
        override fun tryMatch(input: TokenSequence) = tryMatchSequence(matcherFn, input)
    }
}

fun main(args: Array<String>) {
    val code = "import val var"
    var source = object : SourceContentAwareSourceDescriptor() {
        override val sourceLocation = "testcode"
        override val sourceLines = code.split("\n")
    }
    val input = lex(code, source).toTransactional(source.toLocation(1, 1))
    val result = tryMatchSequence({
        keyword(Keyword.IMPORT)
        keyword(Keyword.VAL)
        keyword(Keyword.FUNCTION)
    }, input)
    println("Done")
}