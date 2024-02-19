package io.github.tmarsteel.emerge.backend.llvm

import org.bytedeco.javacpp.BytePointer
import org.bytedeco.javacpp.PointerPointer
import org.bytedeco.llvm.LLVM.LLVMTargetDataRef
import org.bytedeco.llvm.LLVM.LLVMTypeRef
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

internal fun LLVMTypeRef.describeMemoryLayout(targetDataRef: LLVMTargetDataRef): String {
    val sb = StringBuilder()
    describeMemoryLayoutTo(targetDataRef, "", sb, 0)
    return sb.toString()
}

private fun LLVMTypeRef.describeMemoryLayoutTo(
    targetDataRef: LLVMTargetDataRef,
    indent: String,
    out: StringBuilder,
    baseOffset: Int,
) {
    val kind = LLVM.LLVMGetTypeKind(this)
    when (kind) {
        LLVM.LLVMStructTypeKind -> describeStructMemoryLayoutTo(targetDataRef, indent, out, baseOffset)
        LLVM.LLVMArrayTypeKind -> describeArrayMemoryLayoutTo(targetDataRef, indent, out)
        LLVM.LLVMVectorTypeKind,
        LLVM.LLVMScalableVectorTypeKind -> describeVectorMemoryLayoutTo(targetDataRef, indent, out)
        LLVM.LLVMIntegerTypeKind -> {
            out.append("i")
            out.append(LLVM.LLVMGetIntTypeWidth(this))
        }
        LLVM.LLVMVoidTypeKind -> out.append("void")
        LLVM.LLVMPointerTypeKind,
        LLVM.LLVMHalfTypeKind,
        LLVM.LLVMFloatTypeKind,
        LLVM.LLVMBFloatTypeKind,
        LLVM.LLVMDoubleTypeKind,
        LLVM.LLVMX86_FP80TypeKind,
        LLVM.LLVMFP128TypeKind,
        LLVM.LLVMPPC_FP128TypeKind,
        LLVM.LLVMX86_AMXTypeKind,
        LLVM.LLVMX86_MMXTypeKind,
        LLVM.LLVMTargetExtTypeKind,
        LLVM.LLVMLabelTypeKind,
        LLVM.LLVMTokenTypeKind,
        LLVM.LLVMMetadataTypeKind,
        LLVM.LLVMFunctionTypeKind -> out.append(getLlvmMessage(LLVM.LLVMPrintTypeToString(this)))
        else -> throw UnsupportedOperationException()
    }
}

private fun LLVMTypeRef.describeStructMemoryLayoutTo(
    targetDataRef: LLVMTargetDataRef,
    indent: String,
    out: StringBuilder,
    baseOffset: Int,
) {
    val selfSize = LLVM.LLVMSizeOfTypeInBits(targetDataRef, this) / 8
    out.append("(0x")
    out.append(selfSize.toString(16).padStart(2, '0'))
    out.append(") ")

    val selfPrefix = when {
        LLVM.LLVMIsLiteralStruct(this) == 1 -> ""
        else -> "%" + LLVM.LLVMGetStructName(this).string + " "
    }

    out.append(selfPrefix)
    out.append("{\n")

    val nElements = LLVM.LLVMCountStructElementTypes(this)
    val elementsArray = PointerPointer<LLVMTypeRef>(nElements.toLong())
    LLVM.LLVMGetStructElementTypes(this, elementsArray)

    for (memberIndex in 0 until nElements) {
        val memberType = elementsArray.get(LLVMTypeRef::class.java, memberIndex.toLong())
        val offset = baseOffset + LLVM.LLVMOffsetOfElement(targetDataRef, this, memberIndex).toInt()
        out.append(indent)
        out.append("  +0x")
        out.append(offset.toString(16).padStart(2, '0'))
        out.append("  ")
        memberType.describeMemoryLayoutTo(targetDataRef, indent + "  ", out, offset)
        out.append("\n")
    }

    out.append(indent)
    out.append("}")
}

private fun LLVMTypeRef.describeArrayMemoryLayoutTo(
    targetDataRef: LLVMTargetDataRef,
    indent: String,
    out: StringBuilder,
) {
    val elementType = LLVM.LLVMGetElementType(this)
    out.append("[")
    out.append(LLVM.LLVMGetArrayLength2(this).toString())
    out.append(" x ")
    elementType.describeMemoryLayoutTo(targetDataRef, indent + "  ", out, 0)
    out.append("]")
}

private fun LLVMTypeRef.describeVectorMemoryLayoutTo(
    targetDataRef: LLVMTargetDataRef,
    indent: String,
    out: StringBuilder,
) {
    val elementType = LLVM.LLVMGetElementType(this)
    out.append("<")
    out.append(LLVM.LLVMGetVectorSize(this).toString())
    out.append(" x ")
    elementType.describeMemoryLayoutTo(targetDataRef, indent + "  ", out, 0)
    out.append(">")
}