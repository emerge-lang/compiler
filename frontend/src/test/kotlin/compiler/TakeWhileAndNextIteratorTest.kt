package compiler.compiler

import compiler.util.TakeWhileAndNextIterator.Companion.takeWhileAndNext
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class TakeWhileAndNextIteratorTest : FreeSpec({
    "test" {
        val elements = listOf(1, 2, 3, 4, 5, 6, 7, 8)
        val filtered = elements.takeWhileAndNext { it < 4 }.toList()
        filtered shouldBe listOf(1, 2, 3, 4)
    }
})