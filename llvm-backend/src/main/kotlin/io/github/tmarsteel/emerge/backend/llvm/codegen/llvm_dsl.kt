package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocated
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocatedValueBaseType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm

context(BasicBlockBuilder<*, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.anyValueBase(): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
    return this.type.pointed.pointerToCommonBase(this@BasicBlockBuilder, this@anyValueBase)
}

context(BasicBlockBuilder<*, *>)
internal fun LlvmType.sizeof(): LlvmValue<EmergeWordType> {
    return LlvmValue(Llvm.LLVMSizeOf(this.getRawInContext(context)), EmergeWordType)
}