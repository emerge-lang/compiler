package compiler.compiler.parser

import compiler.ast.AstCodeChunk
import compiler.compiler.negative.lexCode
import compiler.lexer.Span
import compiler.parser.grammar.BracedCodeOrSingleStatement
import compiler.parser.grammar.rule.MatchingResult
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldNotBe
import io.kotest.matchers.types.shouldBeInstanceOf

class EmptyCodeBlockTest : FreeSpec({
    "test" {
        val result = BracedCodeOrSingleStatement.match(lexCode("{}", false), 0)
            .filterIsInstance<MatchingResult.Success<*>>()
            .single()
        result.item.shouldBeInstanceOf<AstCodeChunk>()
        (result.item as AstCodeChunk).span shouldNotBe Span.UNKNOWN
    }
})