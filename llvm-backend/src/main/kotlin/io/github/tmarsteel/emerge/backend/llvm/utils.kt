package io.github.tmarsteel.emerge.backend.llvm

fun <T, K> Iterable<T>.associateByErrorOnDuplicate(keySelector: (T) -> K): Map<K, T> {
    val destination = HashMap<K, T>()
    for (e in this) {
        val key = keySelector(e)
        if (destination.putIfAbsent(key, e) != null) {
            throw RuntimeException("Duplicate key: $key")
        }
    }
    return destination
}