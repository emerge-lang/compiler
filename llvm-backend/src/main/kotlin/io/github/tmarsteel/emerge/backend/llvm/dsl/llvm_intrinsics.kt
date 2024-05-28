package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType

internal object UnsignedWordAddWithOverflow : LlvmIntrinsic<UnsignedWordAddWithOverflow.ReturnType>(
    "llvm.uadd.with.overflow",
    listOf(EmergeWordType),
    listOf(EmergeWordType, EmergeWordType),
    ReturnType,
) {
    object ReturnType : LlvmInlineStructType() {
        val result by structMember(EmergeWordType)
        val hadOverflow by structMember(LlvmBooleanType)
    }
}