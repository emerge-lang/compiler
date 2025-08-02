package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocated
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocatedValueBaseType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeS8ArrayType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode

internal fun EmergeLlvmContext.emergeStringLiteral(utf8Bytes: ByteArray): LlvmGlobal<EmergeClassType> {
    val byteArrayConstant = EmergeS8ArrayType.buildConstantIn(
        this,
        utf8Bytes.asList(),
        { i8(it) }
    )
    val byteArrayGlobal = addGlobal(byteArrayConstant, LlvmThreadLocalMode.NOT_THREAD_LOCAL)
    val stringLiteralConstant = stringType.buildStaticConstant(mapOf(
        stringType.irClass.fields.single() to byteArrayGlobal
    ))
    return addGlobal(stringLiteralConstant, LlvmThreadLocalMode.NOT_THREAD_LOCAL)
}

internal fun EmergeLlvmContext.emergeStringLiteral(value: String): LlvmGlobal<EmergeClassType> {
    return emergeStringLiteral(value.toByteArray(Charsets.UTF_8))
}

context(b: BasicBlockBuilder<*, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.anyValueBase(): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
    return this.type.pointed.pointerToCommonBase(b, this@anyValueBase)
}

context(b: BasicBlockBuilder<*, *>)
internal fun LlvmType.sizeof(): LlvmValue<EmergeWordType> {
    return LlvmValue(Llvm.LLVMSizeOf(this.getRawInContext(b.context)), EmergeWordType)
}