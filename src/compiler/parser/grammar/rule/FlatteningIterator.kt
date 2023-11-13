package compiler.parser.grammar.rule

class FlatteningIterator<T> private constructor(
    private val base: Iterator<Iterator<T>>,
) : Iterator<T> {
    private var currentSubIterator = if (base.hasNext()) base.next().iterator() else emptyList<T>().iterator()

    override fun hasNext(): Boolean {
        return currentSubIterator.hasNext() || base.hasNext()
    }

    override fun next(): T {
        if (!currentSubIterator.hasNext()) {
            currentSubIterator = base.next()
        }

        return currentSubIterator.next()
    }

    companion object {
        fun <T> Iterator<Iterator<T>>.flattenRemaining(): Iterator<T> = FlatteningIterator(this)
    }
}