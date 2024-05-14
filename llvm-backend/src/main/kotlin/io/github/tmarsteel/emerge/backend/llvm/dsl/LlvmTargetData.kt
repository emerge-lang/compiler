package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTargetDataRef

class LlvmTargetData(
    val ref: LlvmTargetDataRef
) {
    val pointerSizeInBytes: Int by lazy {
        Llvm.LLVMPointerSize(ref)
    }
}