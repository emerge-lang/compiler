package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.i16
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i64
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word

context(KotlinLlvmFunction.DefinitionReceiver<*, *>)
private fun instructionAliasAttributes() {
    functionAttribute(LlvmFunctionAttribute.AlwaysInline)
    functionAttribute(LlvmFunctionAttribute.NoFree)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
}

private fun <T : LlvmIntegerType> buildUnaryMinusFn(
    emergeTypeSimpleName: String,
    llvmType: T,
    constantFactory: EmergeLlvmContext.(Long) -> LlvmValue<T>,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return KotlinLlvmFunction.define<EmergeLlvmContext, T>(
        "emerge.core.${emergeTypeSimpleName}::unaryMinus",
        llvmType,
    ) {
        instructionAliasAttributes()

        val self by param(llvmType)

        body {
            ret(sub(context.constantFactory(0), self))
        }
    }
}

internal val unaryMinus_s8 = buildUnaryMinusFn("S8", LlvmI8Type) { i8(it.toByte()) }
internal val unaryMinus_s16 = buildUnaryMinusFn("S16", LlvmI16Type) { i16(it.toShort()) }
internal val unaryMinus_s32 = buildUnaryMinusFn("S32", LlvmI32Type) { i32(it.toInt()) }
internal val unaryMinus_s64 = buildUnaryMinusFn("S64", LlvmI64Type) { i64(it) }
internal val unaryMinus_sWord = buildUnaryMinusFn("SWord", EmergeWordType) { word(it) }

private fun <T : LlvmIntegerType> buildNegateFn(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return KotlinLlvmFunction.define<EmergeLlvmContext, T>(
        "emerge.core.${emergeSignedTypeSimpleName}::negate",
        llvmType,
    ) {
        instructionAliasAttributes()

        val self by param(llvmType)

        body {
            ret(not(self))
        }
    }
}

internal val negate_s8 = buildNegateFn("S8", LlvmI8Type)
internal val negate_u8 = negate_s8.createAlias("emerge.core.U8::negate")

internal val negate_s16 = buildNegateFn("S16", LlvmI16Type)
internal val negate_u16 = negate_s16.createAlias("emerge.core.U16::negate")

internal val negate_s32 = buildNegateFn("S32", LlvmI32Type)
internal val negate_u32 = negate_s32.createAlias("emerge.core.U32::negate")

internal val negate_s64 = buildNegateFn("S64", LlvmI64Type)
internal val negate_u64 = negate_s64.createAlias("emerge.core.U64::negate")

internal val negate_sWord = buildNegateFn("SWord", EmergeWordType)
internal val negate_uWord = negate_sWord.createAlias("emerge.core.UWord::negate")