package compiler.util

/**
 * Takes a list of criteria, whichs natural order determines the importance of every criterion.
 * Objects are then sorted by the priority of the most important criterion that applies to them.
 *
 * Allows for stable sort of objects that match the same set of criteria.
 */
class CriteriaComparator<T : Any>(
    criterionPredicatesInOrder: List<(T) -> Boolean>,
) : Comparator<T> {
    val criteria = criterionPredicatesInOrder

    override fun compare(o1: T, o2: T): Int {
        return o1.priority.compareTo(o2.priority)
    }

    private val T.priority: Int get() {
        return criteria
            .indexOfFirst { criterion -> criterion(this) }
            .takeUnless { it == -1 }
            ?: PRIO_MAX
    }

    private companion object {
        const val PRIO_MAX = Int.MAX_VALUE
    }
}