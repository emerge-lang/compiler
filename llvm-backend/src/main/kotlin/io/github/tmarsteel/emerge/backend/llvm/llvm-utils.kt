package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.api.ir.IrFunction
import io.github.tmarsteel.emerge.backend.api.ir.IrPackage
import io.github.tmarsteel.emerge.backend.api.ir.IrSoftwareContext
import io.github.tmarsteel.emerge.backend.api.ir.IrStruct
import org.bytedeco.javacpp.BytePointer
import org.bytedeco.llvm.global.LLVM
import java.nio.ByteBuffer

internal val IrFunction.llvmName: String get() = this.fqn.toString()
internal val IrStruct.llvmName: String get() = this.fqn.toString()

internal val IrSoftwareContext.packagesSeq: Sequence<IrPackage> get() = modules.asSequence()
    .flatMap { it.packages }

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

internal fun getLlvmMessage(message: BytePointer): String {
    val str = message.string
    LLVM.LLVMDisposeMessage(message)
    return str
}