package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeUWordType

internal object UnsignedWordAddWithOverflow : LlvmIntrinsic<UnsignedWordAddWithOverflow.ReturnType>(
    "llvm.uadd.with.overflow",
    listOf(EmergeUWordType),
    listOf(EmergeUWordType, EmergeUWordType),
    ReturnType,
) {
    object ReturnType : LlvmInlineStructType() {
        val result by structMember(EmergeUWordType)
        val hadOverflow by structMember(LlvmBooleanType)
    }
}

class SignedMin<T : LlvmIntegerType>(llvmType: T) : LlvmIntrinsic<T>(
    "llvm.smin",
    listOf(llvmType),
    listOf(llvmType, llvmType),
    llvmType,
)