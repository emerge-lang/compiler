package io.github.tmarsteel.emerge.backend.llvm

import io.kotest.core.spec.IsolationMode
import io.kotest.core.spec.style.FreeSpec
import io.kotest.inspectors.forOne
import io.kotest.matchers.collections.contain
import io.kotest.matchers.collections.haveSize
import io.kotest.matchers.collections.shouldBeSingleton
import io.kotest.matchers.should
import io.kotest.matchers.shouldBe

class PoolerTest : FreeSpec({
    val pooler = Pooler<String>()
    val a = "a"
    val b = "b"
    val c = "c"
    val d = "d"
    val e = "e"

    "all singletons" {
        pooler.mustBeInSamePool(setOf(a))
        pooler.mustBeInSamePool(setOf(b))
        pooler.mustBeInSamePool(setOf(c))
        pooler.mustBeInSamePool(setOf(d))
        pooler.mustBeInSamePool(setOf(e))

        val pools = pooler.pools.toList()
        pools should haveSize(5)
        pools.forOne {
            it.shouldBeSingleton().single() shouldBe a
        }
        pools.forOne {
            it.shouldBeSingleton().single() shouldBe b
        }
        pools.forOne {
            it.shouldBeSingleton().single() shouldBe c
        }
        pools.forOne {
            it.shouldBeSingleton().single() shouldBe d
        }
        pools.forOne {
            it.shouldBeSingleton().single() shouldBe e
        }
    }

    "moving a singleton into a group" {
        pooler.mustBeInSamePool(setOf(a))
        pooler.mustBeInSamePool(setOf(b))
        pooler.mustBeInSamePool(setOf(a, c))

        val pools = pooler.pools.toList()
        pools should haveSize(2)
        pools.forOne {
            it.shouldBeSingleton().single() shouldBe b
        }
        pools.forOne {
            it should haveSize(2)
            it should contain(a)
            it should contain(c)
        }
    }

    "adding to existing pool (multiple each)" {
        pooler.mustBeInSamePool(setOf(a, b))
        pooler.mustBeInSamePool(setOf(c, d))
        pooler.mustBeInSamePool(setOf(d, e))

        val pools = pooler.pools.toList()
        pools should haveSize(2)
        pools.forOne {
            it should haveSize(2)
            it should contain(a)
            it should contain(b)
        }
        pools.forOne {
            it should haveSize(3)
            it should contain(c)
            it should contain(d)
            it should contain(e)
        }
    }

    "merging two pools" {
        val e = "e"
        val f = "f"
        val g = "g"
        val h = "h"

        pooler.mustBeInSamePool(setOf(a, b))
        pooler.mustBeInSamePool(setOf(c, d))
        pooler.mustBeInSamePool(setOf(e, f))
        pooler.mustBeInSamePool(setOf(c, e, g, h))

        val pools = pooler.pools.toList()
        pools should haveSize(2)
        pools.forOne {
            it should haveSize(2)
            it should contain(a)
            it should contain(b)
        }
        pools.forOne {
            it should haveSize(6)
            it should contain(c)
            it should contain(d)
            it should contain(e)
            it should contain(f)
            it should contain(g)
            it should contain(h)
        }
    }

    "adding a singleton that is already in a group" {
        pooler.mustBeInSamePool(setOf(a, b))
        pooler.mustBeInSamePool(setOf(a))

        val pools = pooler.pools.toList()
        pools should haveSize(1)
        pools.forOne {
            it should haveSize(2)
            it should contain(a)
            it should contain(b)
        }
    }
}) {
    override fun isolationMode(): IsolationMode? {
        return IsolationMode.InstancePerLeaf
    }
}