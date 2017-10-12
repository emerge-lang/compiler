package compiler.parser.grammar

import compiler.lexer.SourceContentAwareSourceDescriptor
import compiler.parser.TokenSequence
import compiler.parser.toTransactional
import io.kotlintest.specs.FreeSpec

abstract class GrammarTestCase : FreeSpec() {
    fun lex(code: String): TokenSequence {
        var source = object : SourceContentAwareSourceDescriptor() {
            override val sourceLocation = "testcode"
            override val sourceLines = code.split("\n")
        }

        return compiler.lexer.lex(code, source).toTransactional(source.toLocation(1, 1))
    }
}