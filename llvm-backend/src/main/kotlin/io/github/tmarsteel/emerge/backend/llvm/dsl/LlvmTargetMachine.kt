package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.LLVM.LLVMTargetMachineRef
import org.bytedeco.llvm.global.LLVM

class LlvmTargetMachine(
    val ref: LLVMTargetMachineRef
) {
    val targetData: LlvmTargetData by lazy {
        LlvmTargetData(LLVM.LLVMCreateTargetDataLayout(ref))
    }
}