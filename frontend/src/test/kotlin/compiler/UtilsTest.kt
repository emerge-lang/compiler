package compiler.compiler

import compiler.groupRunsBy
import compiler.pivot
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.collections.shouldBeEmpty
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

    "groupRunsBy" - {
        "empty" {
            emptyList<String>().groupRunsBy { it.first() }.toList().shouldBeEmpty()
        }
        "last run has single element" {
            val elements = listOf(3, 6, 9, 4, 7, 10, 12)
            val runs = elements.groupRunsBy { it % 3 }.toList()
            runs shouldBe listOf(
                Pair(0, listOf(3, 6, 9)),
                Pair(1, listOf(4, 7, 10)),
                Pair(0, listOf(12)),
            )
        }
        "last run has multiple elements" {
            val elements = listOf(3, 6, 9, 4, 7, 10, 12, 15, 18)
            val runs = elements.groupRunsBy { it % 3 }.toList()
            runs shouldBe listOf(
                Pair(0, listOf(3, 6, 9)),
                Pair(1, listOf(4, 7, 10)),
                Pair(0, listOf(12, 15, 18)),
            )
        }
    }
})