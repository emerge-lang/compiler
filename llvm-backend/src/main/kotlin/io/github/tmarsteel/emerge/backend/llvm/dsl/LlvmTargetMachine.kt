package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTargetMachineRef

class LlvmTargetMachine(
    val ref: LlvmTargetMachineRef
) {
    val targetData: LlvmTargetData by lazy {
        LlvmTargetData(Llvm.LLVMCreateTargetDataLayout(ref))
    }
}