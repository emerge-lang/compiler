package kotlinext

import io.kotlintest.specs.StringSpec

class CollectionsTest : StringSpec() { init {
    "[1, 2, 3][0..0] == [1]" {
        listOf(1, 2, 3)[0..0] shouldEqual listOf(1)
    }

    "[1, 2, 3][2..2] == [3]" {
        listOf(1, 2, 3)[2..2] shouldEqual listOf(3)
    }


    "[1, 2, 3][0..1] == [1,2]" {
        listOf(1, 2, 3)[0..1] shouldEqual listOf(1, 2)
    }
    "[1, 2, 3][0..2] == [1,2,3]" {
        listOf(1, 2, 3)[0..2] shouldEqual listOf(1, 2, 3)
    }
}}