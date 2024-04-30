package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.getLlvmMessage
import org.bytedeco.llvm.LLVM.LLVMValueRef
import org.bytedeco.llvm.global.LLVM

/**
 * A type-safe wrapper around [LLVMValueRef].
 * TODO: can this be optimized out to a @JvmInline value type?
 */
open class LlvmValue<out Type : LlvmType>(
    val raw: LLVMValueRef,
    val type: Type,
) {
    fun <NewT : LlvmType> reinterpretAs(type: NewT): LlvmValue<NewT> = LlvmValue(raw, type)
}

class LlvmConstant<out Type : LlvmType>(
    raw: LLVMValueRef,
    type: Type,
) : LlvmValue<Type>(raw, type) {
    init {
        check(LLVM.LLVMIsConstant(raw) == 1)
    }

    override fun toString(): String = getLlvmMessage(LLVM.LLVMPrintValueToString(raw))?.trim() ?: "?"
}

class LlvmGlobal<Type : LlvmType>(
    raw: LLVMValueRef,
    type: Type,
) : LlvmValue<LlvmPointerType<Type>>(raw, pointerTo(type)) {
    init {
        check(LLVM.LLVMIsAGlobalVariable(raw) != null)
    }

    val mode: ThreadLocalMode
        get() = ThreadLocalMode.entries.single { it.llvmKindValue == LLVM.LLVMGetThreadLocalMode(raw) }

    enum class ThreadLocalMode(val llvmKindValue: Int) {
        SHARED(LLVM.LLVMNotThreadLocal),
        LOCAL_DYNAMIC(LLVM.LLVMLocalDynamicTLSModel),
        GENERAL_DYNAMIC(LLVM.LLVMGeneralDynamicTLSModel),
        INITIAL_EXEC(LLVM.LLVMInitialExecTLSModel),
        LOCAL_EXEC(LLVM.LLVMLocalExecTLSModel)
    }
}