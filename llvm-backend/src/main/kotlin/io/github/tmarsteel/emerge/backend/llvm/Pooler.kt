package io.github.tmarsteel.emerge.backend.llvm

import java.util.Collections
import java.util.IdentityHashMap

/**
 * Groups objects of type [T] based on constraints given to an instance of [Pooler] in the form of method calls,
 * e.g. [mustBeInSamePool].
 * After all elements and constraints have been expressed, [pools] will give the groupings that fulfill all the
 * constraints.
 *
 * Grouping is done based on object **identity**.
 */
internal class Pooler<T : Any> {
    private val singletons = IdentitySet<T>()
    private val poolsByElement = IdentityHashMap<T, MutableSet<T>>()
    val pools: Sequence<Set<T>> get() = poolsByElement.values.toSet().asSequence() + singletons.asSequence().map { setOf(it) }

    fun mustBeInSamePool(elements: Collection<T>) {
        if (elements.size == 1) {
            val element = elements.single()
            assureInSomePool(element)
        }

        singletons.removeAll(elements)

        val pools = elements.mapNotNull { poolsByElement[it] }
        if (pools.isEmpty()) {
            addBrandNewPool(elements)
            return
        }

        if (pools.size == 1) {
            pools.single().addAll(elements)
            return
        }

        val mergedPool = IdentitySet<T>()
        pools.forEach(mergedPool::addAll)
        mergedPool.addAll(elements)
        mergedPool.forEach {
            poolsByElement[it] = mergedPool
        }
    }

    /**
     * assures that [pools] has one pool `P` such that `pool.contains(element)`.
     */
    fun assureInSomePool(element: T) {
        if (element in poolsByElement) {
            return
        }

        singletons.add(element)
    }

    private fun addBrandNewPool(pool: Collection<T>) {
        val poolSet = IdentitySet<T>()
        poolSet.addAll(pool)
        for (element in poolSet) {
            poolsByElement[element] = poolSet
        }
    }
}

private fun <T: Any> IdentitySet(): MutableSet<T> = Collections.newSetFromMap(IdentityHashMap())