package io.github.tmarsteel.emerge.backend.llvm.dsl

import io.github.tmarsteel.emerge.backend.llvm.jna.DwarfBaseTypeEncoding
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmMetadataRef
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmTypeRef
import io.github.tmarsteel.emerge.common.EmergeConstants

object LlvmBooleanType : LlvmFixedIntegerType(1u, false, EmergeConstants.CoreModule.BOOLEAN_TYPE_NAME.toString())
object LlvmS8Type : LlvmFixedIntegerType(8u, true, EmergeConstants.CoreModule.S8_TYPE_NAME.toString())
object LlvmU8Type : LlvmFixedIntegerType(8u, false, EmergeConstants.CoreModule.U8_TYPE_NAME.toString())
object LlvmS16Type : LlvmFixedIntegerType(16u, true, EmergeConstants.CoreModule.S16_TYPE_NAME.toString())
object LlvmU16Type : LlvmFixedIntegerType(16u, false, EmergeConstants.CoreModule.S16_TYPE_NAME.toString())
object LlvmS32Type : LlvmFixedIntegerType(32u, true, EmergeConstants.CoreModule.S32_TYPE_NAME.toString())
object LlvmU32Type : LlvmFixedIntegerType(32u, false, EmergeConstants.CoreModule.U32_TYPE_NAME.toString())
object LlvmS64Type : LlvmFixedIntegerType(64u, true, EmergeConstants.CoreModule.S64_TYPE_NAME.toString())
object LlvmU64Type : LlvmFixedIntegerType(64u, false, EmergeConstants.CoreModule.U64_TYPE_NAME.toString())
object LlvmF32Type : LlvmCachedType() {
    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        return Llvm.LLVMFloatTypeInContext(context.ref)
    }

    override fun computeDiType(diBuilder: DiBuilder): LlvmMetadataRef {
        return diBuilder.createBasicType(EmergeConstants.CoreModule.F32_TYPE_NAME.toString(), 32u, DwarfBaseTypeEncoding.FLOAT)
    }
}
object LlvmF64Type : LlvmCachedType() {
    override fun computeRaw(context: LlvmContext): LlvmTypeRef {
        return Llvm.LLVMDoubleTypeInContext(context.ref)
    }

    override fun computeDiType(diBuilder: DiBuilder): LlvmMetadataRef {
        return diBuilder.createBasicType(EmergeConstants.CoreModule.F64_TYPE_NAME.toString(), 64u, DwarfBaseTypeEncoding.FLOAT)
    }
}

fun LlvmContext.i1(value: Boolean): LlvmValue<LlvmBooleanType> {
    return LlvmConstant(
        Llvm.LLVMConstInt(LlvmBooleanType.getRawInContext(this), if (value) 1 else 0, 0),
        LlvmBooleanType,
    )
}

fun LlvmContext.s8(value: Byte): LlvmValue<LlvmS8Type> {
    return LlvmConstant(
        Llvm.LLVMConstInt(LlvmS8Type.getRawInContext(this), value.toLong(), 0),
        LlvmS8Type,
    )
}

fun LlvmContext.u8(value: UByte): LlvmValue<LlvmU8Type> {
    return LlvmConstant(
        Llvm.LLVMConstInt(LlvmU8Type.getRawInContext(this), value.toLong(), 0),
        LlvmU8Type,
    )
}

fun LlvmContext.s16(value: Short): LlvmValue<LlvmS16Type> {
    return LlvmConstant(
        Llvm.LLVMConstInt(LlvmS16Type.getRawInContext(this), value.toLong(), 0),
        LlvmS16Type,
    )
}

fun LlvmContext.u16(value: UShort): LlvmValue<LlvmU16Type> {
    return LlvmConstant(
        Llvm.LLVMConstInt(LlvmU16Type.getRawInContext(this), value.toLong(), 0),
        LlvmU16Type,
    )
}

fun LlvmContext.s32(value: Int): LlvmValue<LlvmS32Type> {
    return LlvmConstant(
        Llvm.LLVMConstInt(LlvmS32Type.getRawInContext(this), value.toLong(), 0),
        LlvmS32Type,
    )
}

fun LlvmContext.u32(value: UInt): LlvmValue<LlvmU32Type> {
    return LlvmConstant(
        Llvm.LLVMConstInt(LlvmU32Type.getRawInContext(this), value.toLong(), 0),
        LlvmU32Type,
    )
}

fun LlvmContext.s64(value: Long): LlvmValue<LlvmS64Type> {
    return LlvmConstant(
        Llvm.LLVMConstInt(LlvmS64Type.getRawInContext(this), value, 0),
        LlvmS64Type,
    )
}

fun LlvmContext.u64(value: ULong): LlvmValue<LlvmU64Type> {
    return LlvmConstant(
        Llvm.LLVMConstInt(LlvmU64Type.getRawInContext(this), value.toLong(), 0),
        LlvmU64Type,
    )
}