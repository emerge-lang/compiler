package io.github.tmarsteel.emerge.backend.llvm

import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTargetDataRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeKind
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef
import io.github.tmarsteel.emerge.backend.llvm.jna.NativePointerArray
import java.nio.ByteBuffer
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.StandardOpenOption

val LlvmTypeRef.isStruct: Boolean
    get() = Llvm.LLVMGetTypeKind(this) == LlvmTypeKind.STRUCT

/**
 * Throws an exception unless
 * * [other] has at least as many members as `this`
 * * matching members in `this` and [other] by index
 *   * the members in both types have the same offset
 *
 * @param inContext requires because the offsets depend on the datalayout
 */
fun requireStructuralSupertypeOf(supertype: LlvmTypeRef, subtype: LlvmTypeRef, targetData: LlvmTargetDataRef) {
    require(supertype.isStruct)
    require(subtype.isStruct)

    val supertypeMemberCount = Llvm.LLVMCountStructElementTypes(supertype)
    val subtypeMemberCount = Llvm.LLVMCountStructElementTypes(subtype)
    require(subtypeMemberCount >= supertypeMemberCount)
    for (index in 0 until supertypeMemberCount) {
        val supertypeOffset = Llvm.LLVMOffsetOfElement(targetData, supertype, index)
        val subtypeOffset = Llvm.LLVMOffsetOfElement(targetData, subtype, index)
        require(supertypeOffset == subtypeOffset) {
            "Struct element #$index has different offsets: $supertypeOffset in supertype, $subtypeOffset in subtype"
        }
    }
}

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

internal fun LlvmTypeRef.describeMemoryLayout(targetDataRef: LlvmTargetDataRef): String {
    val sb = StringBuilder()
    describeMemoryLayoutTo(targetDataRef, "", sb, 0)
    return sb.toString()
}

private fun LlvmTypeRef.describeMemoryLayoutTo(
    targetDataRef: LlvmTargetDataRef,
    indent: String,
    out: StringBuilder,
    baseOffset: Int,
) {
    val kind = Llvm.LLVMGetTypeKind(this)
    when (kind) {
        LlvmTypeKind.STRUCT -> describeStructMemoryLayoutTo(targetDataRef, indent, out, baseOffset)
        LlvmTypeKind.ARRAY -> describeArrayMemoryLayoutTo(targetDataRef, indent, out)
        LlvmTypeKind.VECTOR,
        LlvmTypeKind.SCALABLE_VECTOR -> describeVectorMemoryLayoutTo(targetDataRef, indent, out)
        LlvmTypeKind.INTEGER -> {
            out.append("i")
            out.append(Llvm.LLVMGetIntTypeWidth(this))
        }
        LlvmTypeKind.VOID -> out.append("void")
        LlvmTypeKind.POINTER,
        LlvmTypeKind.HALF,
        LlvmTypeKind.FLOAT,
        LlvmTypeKind.BFLOAT,
        LlvmTypeKind.DOUBLE,
        LlvmTypeKind.X86_FP80,
        LlvmTypeKind.FP128,
        LlvmTypeKind.PPC_FP128,
        LlvmTypeKind.X86_AMX,
        LlvmTypeKind.X86_MMX,
        LlvmTypeKind.TARGETEXT,
        LlvmTypeKind.LABEL,
        LlvmTypeKind.TOKEN,
        LlvmTypeKind.METADATA,
        LlvmTypeKind.FUNCTION -> out.append(Llvm.LLVMPrintTypeToString(this).value)
        else -> throw UnsupportedOperationException()
    }
}

private fun LlvmTypeRef.describeStructMemoryLayoutTo(
    targetDataRef: LlvmTargetDataRef,
    indent: String,
    out: StringBuilder,
    baseOffset: Int,
) {
    val selfSize = Llvm.LLVMSizeOfTypeInBits(targetDataRef, this) / 8
    out.append("(0x")
    out.append(selfSize.toString(16).padStart(2, '0'))
    out.append(") ")

    val selfPrefix = when {
        Llvm.LLVMIsLiteralStruct(this) == 1 -> ""
        else -> "%" + Llvm.LLVMGetStructName(this) + " "
    }

    out.append(selfPrefix)
    out.append("{\n")

    val nElements = Llvm.LLVMCountStructElementTypes(this)
    val elementTypes = NativePointerArray.allocate(nElements, LlvmTypeRef::class.java).use { elementsArray ->
        Llvm.LLVMGetStructElementTypes(this, elementsArray)
        elementsArray.copyToJava()
    }

    for (memberIndex in 0 until nElements) {
        val memberType = elementTypes[memberIndex]
        val offset = baseOffset + Llvm.LLVMOffsetOfElement(targetDataRef, this, memberIndex).toInt()
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

private fun LlvmTypeRef.describeArrayMemoryLayoutTo(
    targetDataRef: LlvmTargetDataRef,
    indent: String,
    out: StringBuilder,
) {
    val elementType = Llvm.LLVMGetElementType(this)
    out.append("[")
    out.append(Llvm.LLVMGetArrayLength2(this).toString())
    out.append(" x ")
    elementType.describeMemoryLayoutTo(targetDataRef, indent + "  ", out, 0)
    out.append("]")
}

private fun LlvmTypeRef.describeVectorMemoryLayoutTo(
    targetDataRef: LlvmTargetDataRef,
    indent: String,
    out: StringBuilder,
) {
    val elementType = Llvm.LLVMGetElementType(this)
    out.append("<")
    out.append(Llvm.LLVMGetVectorSize(this).toString())
    out.append(" x ")
    elementType.describeMemoryLayoutTo(targetDataRef, indent + "  ", out, 0)
    out.append(">")
}