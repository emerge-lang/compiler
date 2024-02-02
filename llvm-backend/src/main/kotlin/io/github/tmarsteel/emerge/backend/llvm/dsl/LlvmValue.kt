package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.LLVM.LLVMValueRef

/**
 * A type-safe wrapper around [LLVMValueRef]
 */
internal class LlvmValue<Type : LlvmType>(
    val raw: LLVMValueRef,
    val type: Type,
)