package io.github.tmarsteel.emerge.backend.llvm

import java.math.BigInteger

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

fun <T, K> Sequence<Pair<K, T>>.associateErrorOnDuplicate(): Map<K, T> {
    val destination = HashMap<K, T>()
    for ((key, e) in this) {
        if (destination.putIfAbsent(key, e) != null) {
            throw RuntimeException("Duplicate key: $key")
        }
    }
    return destination
}

fun UInt.toBigInteger(): BigInteger = BigInteger(
    0,
    byteArrayOf(
        ( this shr 24           ).toByte(),
        ((this shr 16) and 0xFFu).toByte(),
        ((this shr 8)  and 0xFFu).toByte(),
        ( this         and 0xFFu).toByte(),
    ),
)

fun ULong.toBigInteger(): BigInteger = BigInteger(
    0,
    byteArrayOf(
        ( this shr 56           ).toByte(),
        ((this shr 48) and 0xFFu).toByte(),
        ((this shr 40) and 0xFFu).toByte(),
        ((this shr 32) and 0xFFu).toByte(),
        ((this shr 24) and 0xFFu).toByte(),
        ((this shr 16) and 0xFFu).toByte(),
        ( this         and 0xFFu).toByte(),
    ),
)