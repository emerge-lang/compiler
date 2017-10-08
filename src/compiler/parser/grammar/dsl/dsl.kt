package compiler.parser.grammar.dsl

import compiler.lexer.Keyword
import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.lexer.lex
import compiler.matching.ResultCertainty
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

fun eitherOf(mismatchCertainty: ResultCertainty, matcherFn: Grammar): Rule<*> {
    return object : Rule<Any?> {
        override val descriptionOfAMatchingThing = describeEitherOfGrammar(matcherFn)
        override fun tryMatch(input: TokenSequence) = tryMatchEitherOf(matcherFn, input, mismatchCertainty)
    }
}

fun eitherOf(matcherFn: Grammar) = eitherOf(ResultCertainty.NOT_RECOGNIZED, matcherFn)

fun main(args: Array<String>) {
    val code = "import val fun import"
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
        eitherOf {
            keyword(Keyword.EXTERNAL)
            keyword(Keyword.ELSE)
        }
    }
    val result = rule.tryMatch(input)
    println("Done")
}