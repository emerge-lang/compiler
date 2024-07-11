package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmMetadataRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmValueKind
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmValueRef

/**
 * A type-safe wrapper around [LLVMValueRef]
 */
open class LlvmValue<out Type : LlvmType>(
    val raw: LlvmValueRef,
    val type: Type,
) {
    fun <NewT : LlvmType> reinterpretAs(type: NewT): LlvmValue<NewT> = LlvmValue(raw, type)
    fun toMetadata(): LlvmMetadataRef = Llvm.LLVMValueAsMetadata(raw)

    /** for debugging; see [LlvmType.isLlvmAssignableTo] */
    fun isLlvmAssignableTo(target: LlvmType): Boolean {
        return type.isLlvmAssignableTo(target)
    }
}

open class LlvmConstant<out Type : LlvmType>(
    raw: LlvmValueRef,
    type: Type,
) : LlvmValue<Type>(raw, type) {
    init {
        check(Llvm.LLVMIsConstant(raw) == 1)
    }

    override fun toString(): String = Llvm.LLVMPrintValueToString(raw)?.value?.trim() ?: "?"
}

class LlvmGlobal<Type : LlvmType>(
    raw: LlvmValueRef,
    type: Type,
) : LlvmConstant<LlvmPointerType<Type>>(raw, pointerTo(type)) {
    init {
        check(Llvm.LLVMGetValueKind(raw) == LlvmValueKind.GLOBAL_VARIABLE)
    }

    val mode: LlvmThreadLocalMode
        get() = Llvm.LLVMGetThreadLocalMode(raw)
}