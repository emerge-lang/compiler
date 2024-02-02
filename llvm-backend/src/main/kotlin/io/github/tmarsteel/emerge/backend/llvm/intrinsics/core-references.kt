package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.TypeinfoType
import io.github.tmarsteel.emerge.backend.llvm.ValueArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType

internal val getSupertypePointers = LlvmFunction.define<ValueArrayType<LlvmPointerType<TypeinfoType>>>("getSupertypePointers") {
    val inputRef by param(context.pointerToAnyValue)
    getelementptr(inputRef, 0)
    Unit
}