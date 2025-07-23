package compiler.compiler.util

import compiler.util.CriteriaComparator
import io.kotest.core.spec.style.FreeSpec
import io.kotest.matchers.shouldBe

class CriteriaComparatorTest : FreeSpec({
    "base case" {
        val objects = listOf(
            "c1c2__",
            "__c2c3",
            "c1__c3",
        )
        val comparator = CriteriaComparator<String>(listOf(
            { "c1" in it },
            { "c2" in it },
            { "c3" in it },
        ))

        objects.sortedWith(comparator) shouldBe listOf(
            "c1c2__",
            "c1__c3",
            "__c2c3",
        )
    }

    "returns 0 for objects that don't match any criterion" {
        val comparator = CriteriaComparator<String>(listOf(
            { false },
            { false },
            { false },
        ))

        comparator.compare("a", "b") shouldBe 0
    }
})