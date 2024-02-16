package io.github.tmarsteel.emerge.backend.llvm

import org.bytedeco.javacpp.BytePointer
import org.bytedeco.llvm.global.LLVM
import java.nio.ByteBuffer
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.StandardOpenOption

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

internal fun <T> MutableCollection<T>.dropAllAndDo(action: (T) -> Unit) {
    val iterator = iterator()
    while (iterator.hasNext()) {
        val next = iterator.next()
        iterator.remove()
        action(next)
    }
}

internal fun String.copyAsNullTerminated(): ByteArray {
    val notTerminated = encodeToByteArray()
    val buffer = ByteArray(length * 2 + 1)
    encodeToByteArray().copyInto(buffer)

    buffer[buffer.lastIndex] = 0
    return buffer
}

internal fun getLlvmMessage(message: BytePointer): String? {
    val str: String? = message.string
    if (str != null) {
        LLVM.LLVMDisposeMessage(message)
    }
    return str
}

internal fun Path.readToBuffer(): ByteBuffer {
    Files.newByteChannel(this, StandardOpenOption.READ).use { channel ->
        check(channel.size() <= Int.MAX_VALUE)
        val buffer = ByteBuffer.allocateDirect(channel.size().toInt())
        while (buffer.position() < buffer.limit()) {
            channel.read(buffer)
        }
        buffer.flip()

        return buffer
    }
}

internal fun Path.writeBuffer(buffer: ByteBuffer) {
    Files.newByteChannel(this, StandardOpenOption.CREATE, StandardOpenOption.WRITE).use { channel ->
        while (buffer.remaining() > 0) {
            channel.write(buffer)
        }
    }
}