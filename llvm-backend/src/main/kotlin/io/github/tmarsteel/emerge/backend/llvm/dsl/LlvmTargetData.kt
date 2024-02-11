package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.LLVM.LLVMTargetDataRef
import org.bytedeco.llvm.global.LLVM

class LlvmTargetData(
    val ref: LLVMTargetDataRef
) {
    val pointerSizeInBytes: Int by lazy {
        LLVM.LLVMPointerSize(ref)
    }
}