package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.LLVM.LLVMTypeRef
import org.bytedeco.llvm.LLVM.LLVMValueRef

data class LlvmFunction<R : LlvmType>(
    val raw: LLVMValueRef,
    val rawFunctionType: LLVMTypeRef,
    val returnType: R,
    val parameterTypes: List<LlvmType>,
)