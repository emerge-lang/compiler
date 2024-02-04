package io.github.tmarsteel.emerge.backend.llvm.dsl

import org.bytedeco.llvm.global.LLVM

object LlvmBooleanType : LlvmFixedIntegerType(1)
object LlvmI8Type : LlvmFixedIntegerType(8)
object LlvmI16Type : LlvmFixedIntegerType(16)
object LlvmI32Type : LlvmFixedIntegerType(32)
object LlvmI64Type : LlvmFixedIntegerType(64)

fun LlvmContext.i32(value: Int): LlvmValue<LlvmI32Type> {
    return LlvmValue(
        LLVM.LLVMConstInt(LlvmI32Type.getRawInContext(this), value.toLong(), 0),
        LlvmI32Type,
    )
}