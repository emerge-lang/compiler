package io.github.tmarsteel.emerge.backend.llvm.codegen

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.AnyValueType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeHeapAllocated
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.LlvmWordType

context(BasicBlockBuilder<*, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.anyValueBase(): GetElementPointerStep<AnyValueType> {
    return this.type.pointed.pointerToAnyValueBase(this@BasicBlockBuilder, this@anyValueBase)
}

context(BasicBlockBuilder<*, *>)
internal fun LlvmType.sizeof(): LlvmValue<LlvmWordType> {
    // thanks to https://stackoverflow.com/questions/14608250/how-can-i-find-the-size-of-a-type
    val pointerFromNullToSize = getelementptr(
        context.nullValue(LlvmPointerType(this)),
        context.i32(1)
    )
        .get()

    return ptrtoint(pointerFromNullToSize, LlvmWordType)
}