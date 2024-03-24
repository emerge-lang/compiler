package io.github.tmarsteel.emerge.backend.llvm.dsl

data class LlvmFunction<out R : LlvmType>(
    val address: LlvmConstant<LlvmFunctionAddressType>,
    val type: LlvmFunctionType<R>,
)