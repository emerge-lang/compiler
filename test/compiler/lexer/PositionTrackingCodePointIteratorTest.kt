package compiler.compiler.lexer

import compiler.lexer.CodePoint
import compiler.lexer.PositionTrackingCodePointTransactionalSequence
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class PositionTrackingCodePointIteratorTest : FreeSpec({
    "starts at line 1 column 0" {
        val code = "abc"
        val iterator = PositionTrackingCodePointTransactionalSequence(code)

        iterator.currentPosition.lineNumber shouldBe 1u
        iterator.currentPosition.columnNumber shouldBe 0u
    }

    "handles characters on single line" {
        val code = "abc"
        val iterator = PositionTrackingCodePointTransactionalSequence(code)

        iterator.nextOrThrow() shouldBe CodePoint('a'.code)
        iterator.currentPosition.lineNumber shouldBe 1u
        iterator.currentPosition.columnNumber shouldBe 1u
        iterator.currentPosition.codePointIndex shouldBe 0

        iterator.nextOrThrow() shouldBe CodePoint('b'.code)
        iterator.currentPosition.lineNumber shouldBe 1u
        iterator.currentPosition.columnNumber shouldBe 2u
        iterator.currentPosition.codePointIndex shouldBe 1

        iterator.nextOrThrow() shouldBe CodePoint('c'.code)
        iterator.currentPosition.lineNumber shouldBe 1u
        iterator.currentPosition.columnNumber shouldBe 3u
        iterator.currentPosition.codePointIndex shouldBe 2
    }

    "handles newlines (LF codepoint)" {
        val code = "ab\ncd\n\nef"
        val iterator = PositionTrackingCodePointTransactionalSequence(code)

        iterator.nextOrThrow() shouldBe CodePoint('a'.code)
        iterator.currentPosition.lineNumber shouldBe 1u
        iterator.currentPosition.columnNumber shouldBe 1u
        iterator.currentPosition.codePointIndex shouldBe 0

        iterator.nextOrThrow() shouldBe CodePoint('b'.code)
        iterator.currentPosition.lineNumber shouldBe 1u
        iterator.currentPosition.columnNumber shouldBe 2u
        iterator.currentPosition.codePointIndex shouldBe 1

        iterator.nextOrThrow() shouldBe CodePoint('\n'.code)
        iterator.currentPosition.lineNumber shouldBe 1u
        iterator.currentPosition.columnNumber shouldBe 3u
        iterator.currentPosition.codePointIndex shouldBe 2

        iterator.nextOrThrow() shouldBe CodePoint('c'.code)
        iterator.currentPosition.lineNumber shouldBe 2u
        iterator.currentPosition.columnNumber shouldBe 1u
        iterator.currentPosition.codePointIndex shouldBe 3

        iterator.nextOrThrow() shouldBe CodePoint('d'.code)
        iterator.currentPosition.lineNumber shouldBe 2u
        iterator.currentPosition.columnNumber shouldBe 2u
        iterator.currentPosition.codePointIndex shouldBe 4

        iterator.nextOrThrow() shouldBe CodePoint('\n'.code)
        iterator.currentPosition.lineNumber shouldBe 2u
        iterator.currentPosition.columnNumber shouldBe 3u
        iterator.currentPosition.codePointIndex shouldBe 5

        iterator.nextOrThrow() shouldBe CodePoint('\n'.code)
        iterator.currentPosition.lineNumber shouldBe 3u
        iterator.currentPosition.columnNumber shouldBe 1u
        iterator.currentPosition.codePointIndex shouldBe 6

        iterator.nextOrThrow() shouldBe CodePoint('e'.code)
        iterator.currentPosition.lineNumber shouldBe 4u
        iterator.currentPosition.columnNumber shouldBe 1u
        iterator.currentPosition.codePointIndex shouldBe 7

        iterator.nextOrThrow() shouldBe CodePoint('f'.code)
        iterator.currentPosition.lineNumber shouldBe 4u
        iterator.currentPosition.columnNumber shouldBe 2u
        iterator.currentPosition.codePointIndex shouldBe 8
    }
})