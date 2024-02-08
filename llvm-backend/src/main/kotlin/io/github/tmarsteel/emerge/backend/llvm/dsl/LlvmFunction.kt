package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.LLVM.LLVMTypeRef

data class LlvmFunction<R : LlvmType>(
    val address: LlvmConstant<LlvmFunctionAddressType>,
    val rawFunctionType: LLVMTypeRef,
    val returnType: R,
    val parameterTypes: List<LlvmType>,
)