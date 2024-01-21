package compiler.compiler

import compiler.pivot
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class UtilsTest : FreeSpec({
    "pivot" - {
        "of single sequence" {
            val source = sequenceOf(sequenceOf(1, 2, 3, 4))
            source.pivot().toList() shouldBe listOf(listOf(1), listOf(2), listOf(3), listOf(4))
        }

        "of multiple same length" {
            val source = sequenceOf(
                sequenceOf(1, 2, 3, 4),
                sequenceOf(5, 6, 7, 8)
            )
            source.pivot().toList() shouldBe listOf(listOf(1, 5), listOf(2, 6), listOf(3, 7), listOf(4, 8))
        }

        "of multiple differing lengths" {
            val source = sequenceOf(
                sequenceOf(1, 2, 3, 4),
                sequenceOf(5, 6, 7, 8, 9, 10),
                sequenceOf(11, 12)
            )
            source.pivot().toList() shouldBe listOf(
                listOf(1, 5, 11),
                listOf(2, 6, 12),
                listOf(3, 7, null),
                listOf(4, 8, null),
                listOf(null, 9, null),
                listOf(null, 10, null),
            )
        }
    }
})