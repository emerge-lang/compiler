package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM

/**
 * A type-safe wrapper around [LLVMValueRef].
 * TODO: can this be optimized out to a @JvmInline value type?
 */
class LlvmValue<out Type : LlvmType>(
    val raw: LLVMValueRef,
    val type: Type,
) {
    val isConstant: Boolean
        get() = LLVM.LLVMIsConstant(raw) == 1
}