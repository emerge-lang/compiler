package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocated
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocatedValueBaseType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType

context(BasicBlockBuilder<*, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.anyValueBase(): GetElementPointerStep<EmergeHeapAllocatedValueBaseType> {
    return this.type.pointed.pointerToCommonBase(this@BasicBlockBuilder, this@anyValueBase)
}

context(BasicBlockBuilder<*, *>)
internal fun LlvmType.sizeof(): LlvmValue<EmergeWordType> {
    // thanks to https://stackoverflow.com/questions/14608250/how-can-i-find-the-size-of-a-type
    val pointerFromNullToSize = getelementptr(
        context.nullValue(LlvmPointerType(this)),
        context.i32(1)
    )
        .get()

    return ptrtoint(pointerFromNullToSize, EmergeWordType)
}