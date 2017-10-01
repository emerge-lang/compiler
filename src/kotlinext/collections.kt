package kotlinext

operator fun <T> Array<T>.get(range: IntRange): Iterable<T> = asList()[range]

operator fun <T> Collection<T>.get(range: IntRange): List<T> {
    if (range.first < 0 || range.last < 0) throw IllegalArgumentException("Range first and last must be >= 0")

    if (range.first > size - 1 || range.last > size - 1) {
        throw ArrayIndexOutOfBoundsException()
    }

    var list = ArrayList<T>(range.last - range.first + 1)
    val iterator = iterator()

    for (i in 0 .. range.first - 1) iterator.next()
    for (i in range) {
        list.add(iterator.next())
    }
    return list
}