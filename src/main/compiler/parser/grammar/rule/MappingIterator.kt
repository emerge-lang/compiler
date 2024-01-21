package compiler.parser.grammar.rule

class MappingIterator<T, M> private constructor(
    private val base: Iterator<T>,
    private val transform: (Int, T) -> M,
) : Iterator<M> {
    private var index = 0
    override fun hasNext(): Boolean {
        return base.hasNext()
    }

    override fun next(): M {
        return transform(index++, base.next())
    }

    companion object {
        @JvmStatic
        fun <T, M> Iterator<T>.mapRemainingIndexed(transform: (Int, T) -> M): Iterator<M> = MappingIterator(this, transform)
    }
}