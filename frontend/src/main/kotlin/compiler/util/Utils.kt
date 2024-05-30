package compiler.util

import java.util.IdentityHashMap

/**
 * If any of the elements maps to `true`, this short-circuits to `true`. If all elements return `null`,
 * also returns `null`. Returns `false` iff all elements map to `false`.
 */
fun <T : Any> Iterable<T>.mapNullableBoolReduceOr(onEmpty: Boolean?, map: (T) -> Boolean?): Boolean? {
    val iterator = iterator()
    if (!iterator.hasNext()) {
        return onEmpty
    }
    var someNull = false
    var carry = false
    while (iterator.hasNext()) {
        val next = map(iterator.next())
        if (next == null) {
            someNull = true
        } else {
            carry = carry || next
        }
    }

    if (carry) {
        return true
    }

    if (someNull) {
        return null
    }

    return false
}

/**
 * Arranges the given elements such that for any element `e` its index `i` in the output is greater than the index
 * of all of its dependencies according to `dependsOn`.
 * @param dependsOn returns `true` when `dependency` is a dependency of `element`, false otherwise.
 */
fun <T : Any> Iterable<T>.sortedTopologically(dependsOn: (element: T, dependency: T) -> Boolean): List<T> {
    val elementsToSort: MutableMap<T, List<T>> = this.associateWithTo(IdentityHashMap()) { element ->
        this.filter { possibleDependency -> possibleDependency !== element && dependsOn(element, possibleDependency) }
    }

    val sorted = ArrayList<T>(elementsToSort.size)
    while (elementsToSort.isNotEmpty()) {
        var anyRemoved = false
        val elementsIterator = elementsToSort.iterator()
        while (elementsIterator.hasNext()) {
            val (element, dependencies) = elementsIterator.next()
            if (dependencies.none { it in elementsToSort }) {
                // no dependency to be sorted -> all are sorted
                sorted.add(element)
                elementsIterator.remove()
                anyRemoved = true
            }
        }

        if (!anyRemoved) {
            throw RuntimeException("Cyclic dependency involving ${elementsToSort.firstNotNullOf { it.key }}")
        }
    }

    return sorted
}

/**
 * @return all the 0th, 1st, 2nd, ... elements of the sub-sequences in a list each
 */
fun <T : Any> Sequence<Sequence<T>>.pivot(): Sequence<List<T?>> {
    return object : Sequence<List<T?>> {
        override fun iterator(): Iterator<List<T?>> {
            val subSequenceIterators = this@pivot.mapIndexed { _, it -> it.iterator() }.toList()
            return object : Iterator<List<T?>> {
                private var next: List<T?>? = null

                private fun tryFindNext() {
                    if (next != null) {
                        return
                    }

                    next = subSequenceIterators
                        .map { if (it.hasNext()) it.next() else null }
                        .takeIf { it.any { e -> e != null }}
                }

                override fun hasNext(): Boolean {
                    tryFindNext()

                    return next != null
                }

                override fun next(): List<T?> {
                    tryFindNext()
                    val nextLocal = next ?: throw NoSuchElementException()
                    next = null
                    return nextLocal
                }
            }
        }
    }
}

fun <T> List<T>.twoElementPermutationsUnordered(): Sequence<Pair<T, T>> {
    require(this is RandomAccess)
    return sequence {
        for (outerIndex in 0..this@twoElementPermutationsUnordered.lastIndex) {
            for (innerIndex in outerIndex + 1 .. this@twoElementPermutationsUnordered.lastIndex) {
                yield(Pair(
                    this@twoElementPermutationsUnordered[outerIndex],
                    this@twoElementPermutationsUnordered[innerIndex],
                ))
            }
        }
    }
}

fun <T, K> Iterable<T>.groupRunsBy(runKeyEquals: (K, K) -> Boolean = { a, b -> a == b }, runKeySelector: (T) -> K): Iterable<Pair<K, List<T>>> = object : Iterable<Pair<K, List<T>>> {
    override fun iterator(): Iterator<Pair<K, List<T>>> {
        val baseIterator = this@groupRunsBy.iterator()
        if (!baseIterator.hasNext()) {
            return emptyList<Pair<K, List<T>>>().iterator()
        }
        return object : Iterator<Pair<K, List<T>>> {
            val firstElement = baseIterator.next()
            var currentKey: K = runKeySelector(firstElement)
            var currentRun: MutableList<T> = ArrayList()
            init {
                currentRun.add(firstElement)
            }
            private var lastRunYielded = false
            override fun hasNext(): Boolean {
                return baseIterator.hasNext() || !lastRunYielded
            }
            override fun next(): Pair<K, List<T>> {
                while(baseIterator.hasNext()) {
                    val nextElement = baseIterator.next()
                    val nextElementKey = runKeySelector(nextElement)
                    if (!runKeyEquals(currentKey, nextElementKey)) {
                        val keyToYield = currentKey
                        val runToYield = currentRun
                        currentRun = ArrayList()
                        currentRun.add(nextElement)
                        currentKey = nextElementKey
                        return Pair(keyToYield, runToYield)
                    }

                    currentRun.add(nextElement)
                }

                if (lastRunYielded) {
                    throw NoSuchElementException()
                } else {
                    lastRunYielded = true
                    return Pair(currentKey, currentRun)
                }
            }
        }
    }
}