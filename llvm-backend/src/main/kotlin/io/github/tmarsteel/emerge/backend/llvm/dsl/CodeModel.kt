package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.global.LLVM


enum class CodeModel(val numeric: Int) {
    DEFAULT(LLVM.LLVMCodeModelDefault),
    JIT_DEFAULT(LLVM.LLVMCodeModelJITDefault),
    TINY(LLVM.LLVMCodeModelTiny),
    SMALL(LLVM.LLVMCodeModelSmall),
    KERNEL(LLVM.LLVMCodeModelKernel),
    MEDIUM(LLVM.LLVMCodeModelMedium),
    LARGE(LLVM.LLVMCodeModelLarge),
}