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
    val criteria = criterionPredicatesInOrder.asSequence()

    override fun compare(o1: T, o2: T): Int {
        return o1.priority.compareTo(o2.priority)
    }

    private val T.priority: UInt get() {
        return criteria
            .mapIndexedNotNull { index, criterion -> index.takeIf { criterion(this) } }
            .firstOrNull()
            ?.toUInt()
            ?: PRIO_MAX
    }

    private companion object {
        val PRIO_MAX = Int.MAX_VALUE.toUInt()
    }
}