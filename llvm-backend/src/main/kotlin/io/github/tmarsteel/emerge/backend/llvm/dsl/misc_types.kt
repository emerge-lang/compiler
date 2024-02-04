package io.github.tmarsteel.emerge.backend.llvm.dsl

object LlvmGlobalCtorEntry : LlvmStructType("global_ctor_entry") {
    val priority by structMember(LlvmI32Type)
    val function by structMember(LlvmFunctionAddressType)
    val data by structMember(LlvmPointerType(LlvmVoidType))
}