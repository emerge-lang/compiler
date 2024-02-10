package io.github.tmarsteel.emerge.backend.llvm

import org.bytedeco.javacpp.BytePointer
import org.bytedeco.llvm.global.LLVM

internal fun <T : Any> iterateLinkedList(
    first: T?,
    next: (T) -> T?
): Sequence<T> = sequence {
    var pivot = first
    while (pivot != null) {
        yield(pivot)
        pivot = next(pivot)
    }
}

internal fun <K, V> MutableMap<K, V>.dropAllAndDo(action: (Map.Entry<K, V>) -> Unit) {
    val iterator = iterator()
    while (iterator.hasNext()) {
        val next = iterator.next()
        iterator.remove()
        action(next)
    }
}

internal fun getLlvmMessage(message: BytePointer): String? {
    val str: String? = message.string
    if (str != null) {
        LLVM.LLVMDisposeMessage(message)
    }
    return str
}