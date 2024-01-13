package compiler.compiler.lexer

import compiler.lexer.PositionTrackingCodePointIterator
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class PositionTrackingCodePointIteratorTest : FreeSpec({
    "starts at line 1 column 0" {
        val code = "abc"
        val iterator = PositionTrackingCodePointIterator(code)

        iterator.currentLineNumber shouldBe 1u
        iterator.currentColumnNumber shouldBe 0u
    }

    "handles characters on single line" {
        val code = "abc"
        val iterator = PositionTrackingCodePointIterator(code)

        iterator.next() shouldBe 'a'.code
        iterator.currentLineNumber shouldBe 1u
        iterator.currentColumnNumber shouldBe 1u

        iterator.next() shouldBe 'b'.code
        iterator.currentLineNumber shouldBe 1u
        iterator.currentColumnNumber shouldBe 2u

        iterator.next() shouldBe 'c'.code
        iterator.currentLineNumber shouldBe 1u
        iterator.currentColumnNumber shouldBe 3u
    }

    "handles newlines (LF codepoint)" {
        val code = "ab\ncd\n\nef"
        val iterator = PositionTrackingCodePointIterator(code)

        iterator.next() shouldBe 'a'.code
        iterator.currentLineNumber shouldBe 1u
        iterator.currentColumnNumber shouldBe 1u

        iterator.next() shouldBe 'b'.code
        iterator.currentLineNumber shouldBe 1u
        iterator.currentColumnNumber shouldBe 2u

        iterator.next() shouldBe '\n'.code
        iterator.currentLineNumber shouldBe 1u
        iterator.currentColumnNumber shouldBe 3u

        iterator.next() shouldBe 'c'.code
        iterator.currentLineNumber shouldBe 2u
        iterator.currentColumnNumber shouldBe 1u

        iterator.next() shouldBe 'd'.code
        iterator.currentLineNumber shouldBe 2u
        iterator.currentColumnNumber shouldBe 2u

        iterator.next() shouldBe '\n'.code
        iterator.currentLineNumber shouldBe 2u
        iterator.currentColumnNumber shouldBe 3u

        iterator.next() shouldBe '\n'.code
        iterator.currentLineNumber shouldBe 3u
        iterator.currentColumnNumber shouldBe 1u

        iterator.next() shouldBe 'e'.code
        iterator.currentLineNumber shouldBe 4u
        iterator.currentColumnNumber shouldBe 1u

        iterator.next() shouldBe 'f'.code
        iterator.currentLineNumber shouldBe 4u
        iterator.currentColumnNumber shouldBe 2u
    }
})