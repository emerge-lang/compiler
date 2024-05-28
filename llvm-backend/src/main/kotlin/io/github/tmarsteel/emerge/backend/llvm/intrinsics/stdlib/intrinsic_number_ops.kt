package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFixedIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmInlineStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntegerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmIntrinsic
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.i16
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i64
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.inlinePanic
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.word
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate

internal val intrinsicNumberOperations: List<KotlinLlvmFunction<EmergeLlvmContext, out LlvmIntegerType>> by lazy {
    listOf(
        unaryMinus_s8,
        unaryMinus_s16,
        unaryMinus_s32,
        unaryMinus_s64,
        unaryMinus_sWord,
        negate_s8,
        negate_u8,
        negate_s16,
        negate_u16,
        negate_s32,
        negate_u32,
        negate_s64,
        negate_u64,
        negate_sWord,
        negate_uWord,
        plus_s8,
        plus_u8,
        plus_s16,
        plus_u16,
        plus_s32,
        plus_u32,
        plus_s64,
        plus_u64,
        plus_sWord,
        plus_uWord,
        minus_s8,
        minus_u8,
        minus_s16,
        minus_u16,
        minus_s32,
        minus_u32,
        minus_s64,
        minus_u64,
        minus_sWord,
        minus_uWord,
        times_s8,
        times_u8,
        times_s16,
        times_u16,
        times_s32,
        times_u32,
        times_s64,
        times_u64,
        times_sWord,
        times_uWord,
        divideBy_s8,
        divideBy_u8,
        divideBy_s16,
        divideBy_u16,
        divideBy_s32,
        divideBy_u32,
        divideBy_s64,
        divideBy_u64,
        divideBy_sWord,
        divideBy_uWord,
        compareTo_s8,
        compareTo_u8,
        compareTo_s16,
        compareTo_u16,
        compareTo_s32,
        compareTo_u32,
        compareTo_s64,
        compareTo_u64,
        compareTo_sWord,
        compareTo_uWord,
        convert_s8_to_s64,
        convert_s16_to_s64,
        convert_s32_to_s64,
        convert_u8_to_u64,
        convert_u16_to_u64,
        convert_u32_to_u64,
    )
}

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
    return KotlinLlvmFunction.define(
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

private val unaryMinus_s8 = buildUnaryMinusFn("S8", LlvmI8Type) { i8(it.toByte()) }
private val unaryMinus_s16 = buildUnaryMinusFn("S16", LlvmI16Type) { i16(it.toShort()) }
private val unaryMinus_s32 = buildUnaryMinusFn("S32", LlvmI32Type) { i32(it.toInt()) }
private val unaryMinus_s64 = buildUnaryMinusFn("S64", LlvmI64Type) { i64(it) }
private val unaryMinus_sWord = buildUnaryMinusFn("SWord", EmergeWordType) { word(it) }

private fun <T : LlvmIntegerType> buildNegateFn(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return KotlinLlvmFunction.define(
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

private val negate_s8 = buildNegateFn("S8", LlvmI8Type)
private val negate_u8 = negate_s8.createAlias("emerge.core.U8::negate")

private val negate_s16 = buildNegateFn("S16", LlvmI16Type)
private val negate_u16 = negate_s16.createAlias("emerge.core.U16::negate")

private val negate_s32 = buildNegateFn("S32", LlvmI32Type)
private val negate_u32 = negate_s32.createAlias("emerge.core.U32::negate")

private val negate_s64 = buildNegateFn("S64", LlvmI64Type)
private val negate_u64 = negate_s64.createAlias("emerge.core.U64::negate")

private val negate_sWord = buildNegateFn("SWord", EmergeWordType)
private val negate_uWord = negate_sWord.createAlias("emerge.core.UWord::negate")

private fun <T : LlvmIntegerType> buildBinaryOpWithOverflow(
    emergeFunctionCanonicalName: String,
    llvmIntrinsicName: String,
    llvmType: T,
    panicMessage: String,
): KotlinLlvmFunction<EmergeLlvmContext, T> {
    val llvmIntrinsic = LlvmIntrinsic(
        llvmIntrinsicName,
        listOf(llvmType),
        listOf(llvmType, llvmType),
        object : LlvmInlineStructType() {
            val result by structMember(llvmType)
            val hadOverflow by structMember(LlvmBooleanType)
        },
    )

    return KotlinLlvmFunction.define(
        emergeFunctionCanonicalName,
        llvmType,
    ) {
        functionAttribute(LlvmFunctionAttribute.NoFree)
        functionAttribute(LlvmFunctionAttribute.NoRecurse)
        functionAttribute(LlvmFunctionAttribute.WillReturn)
        functionAttribute(LlvmFunctionAttribute.AlwaysInline)

        val operand1 by param(llvmType)
        val operand2 by param(llvmType)

        body {
            val intrinsicResult = call(llvmIntrinsic, listOf(operand1, operand2))
            conditionalBranch(
                condition = extractValue(intrinsicResult) { hadOverflow },
                ifTrue = {
                    inlinePanic(panicMessage)
                }
            )
            ret(extractValue(intrinsicResult) { result })
        }
    }
}

private fun <T : LlvmIntegerType> buildSignedAdditionWithOverflow(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return buildBinaryOpWithOverflow(
        "emerge.core.${emergeSignedTypeSimpleName}::plus",
        "llvm.sadd.with.overflow.*",
        llvmType,
        "Signed integer addition overflow",
    )
}

private fun <T : LlvmIntegerType> buildUnsignedAdditionWithOverflow(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return buildBinaryOpWithOverflow(
        "emerge.core.${emergeSignedTypeSimpleName}::plus",
        "llvm.uadd.with.overflow.*",
        llvmType,
        "Unsigned integer addition overflow",
    )
}

private val plus_s8 = buildSignedAdditionWithOverflow("S8", LlvmI8Type)
private val plus_u8 = buildUnsignedAdditionWithOverflow("U8", LlvmI8Type)
private val plus_s16 = buildSignedAdditionWithOverflow("S16", LlvmI16Type)
private val plus_u16 = buildUnsignedAdditionWithOverflow("U16", LlvmI16Type)
private val plus_s32 = buildSignedAdditionWithOverflow("S32", LlvmI32Type)
private val plus_u32 = buildUnsignedAdditionWithOverflow("U32", LlvmI32Type)
private val plus_s64 = buildSignedAdditionWithOverflow("S64", LlvmI64Type)
private val plus_u64 = buildUnsignedAdditionWithOverflow("U64", LlvmI64Type)
private val plus_sWord = buildSignedAdditionWithOverflow("SWord", EmergeWordType)
private val plus_uWord = buildUnsignedAdditionWithOverflow("UWord", EmergeWordType)

private fun <T : LlvmIntegerType> buildSignedSubtractionWithOverflow(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return buildBinaryOpWithOverflow(
        "emerge.core.${emergeSignedTypeSimpleName}::minus",
        "llvm.ssub.with.overflow.*",
        llvmType,
        "Signed integer subtraction overflow",
    )
}

private fun <T : LlvmIntegerType> buildUnsignedSubtractionWithOverflow(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return buildBinaryOpWithOverflow(
        "emerge.core.${emergeSignedTypeSimpleName}::minus",
        "llvm.usub.with.overflow.*",
        llvmType,
        "Unsigned integer subtraction overflow",
    )
}

private val minus_s8 = buildSignedSubtractionWithOverflow("S8", LlvmI8Type)
private val minus_u8 = buildUnsignedSubtractionWithOverflow("U8", LlvmI8Type)
private val minus_s16 = buildSignedSubtractionWithOverflow("S16", LlvmI16Type)
private val minus_u16 = buildUnsignedSubtractionWithOverflow("U16", LlvmI16Type)
private val minus_s32 = buildSignedSubtractionWithOverflow("S32", LlvmI32Type)
private val minus_u32 = buildUnsignedSubtractionWithOverflow("U32", LlvmI32Type)
private val minus_s64 = buildSignedSubtractionWithOverflow("S64", LlvmI64Type)
private val minus_u64 = buildUnsignedSubtractionWithOverflow("U64", LlvmI64Type)
private val minus_sWord = buildSignedSubtractionWithOverflow("SWord", EmergeWordType)
private val minus_uWord = buildUnsignedSubtractionWithOverflow("UWord", EmergeWordType)

private fun <T : LlvmIntegerType> buildSignedMultiplicationWithOverflow(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return buildBinaryOpWithOverflow(
        "emerge.core.${emergeSignedTypeSimpleName}::times",
        "llvm.smul.with.overflow.*",
        llvmType,
        "Signed integer multiplication overflow",
    )
}

private fun <T : LlvmIntegerType> buildUnsignedMultiplicationWithOverflow(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return buildBinaryOpWithOverflow(
        "emerge.core.${emergeSignedTypeSimpleName}::times",
        "llvm.umul.with.overflow.*",
        llvmType,
        "Unsigned integer multiplication overflow",
    )
}

private val times_s8 = buildSignedMultiplicationWithOverflow("S8", LlvmI8Type)
private val times_u8 = buildUnsignedMultiplicationWithOverflow("U8", LlvmI8Type)
private val times_s16 = buildSignedMultiplicationWithOverflow("S16", LlvmI16Type)
private val times_u16 = buildUnsignedMultiplicationWithOverflow("U16", LlvmI16Type)
private val times_s32 = buildSignedMultiplicationWithOverflow("S32", LlvmI32Type)
private val times_u32 = buildUnsignedMultiplicationWithOverflow("U32", LlvmI32Type)
private val times_s64 = buildSignedMultiplicationWithOverflow("S64", LlvmI64Type)
private val times_u64 = buildUnsignedMultiplicationWithOverflow("U64", LlvmI64Type)
private val times_sWord = buildSignedMultiplicationWithOverflow("SWord", EmergeWordType)
private val times_uWord = buildUnsignedMultiplicationWithOverflow("UWord", EmergeWordType)

private fun <T : LlvmIntegerType> buildSignedDivisionWithZeroCheck(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return KotlinLlvmFunction.define(
        "emerge.core.${emergeSignedTypeSimpleName}::divideBy",
        llvmType,
    ) {
        instructionAliasAttributes()

        val operand1 by param(llvmType)
        val operand2 by param(llvmType)

        body {
            conditionalBranch(
                condition = isZero(operand2),
                ifTrue = {
                    inlinePanic("division by zero")
                }
            )

            ret(sdiv(operand1, operand2))
        }
    }
}

private fun <T : LlvmIntegerType> buildUnsignedDivisionWithZeroCheck(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return KotlinLlvmFunction.define(
        "emerge.core.${emergeSignedTypeSimpleName}::divideBy",
        llvmType,
    ) {
        instructionAliasAttributes()

        val operand1 by param(llvmType)
        val operand2 by param(llvmType)

        body {
            conditionalBranch(
                condition = isZero(operand2),
                ifTrue = {
                    inlinePanic("division by zero")
                }
            )

            ret(udiv(operand1, operand2))
        }
    }
}

private val divideBy_s8 = buildSignedDivisionWithZeroCheck("S8", LlvmI8Type)
private val divideBy_u8 = buildUnsignedDivisionWithZeroCheck("U8", LlvmI8Type)
private val divideBy_s16 = buildSignedDivisionWithZeroCheck("S16", LlvmI16Type)
private val divideBy_u16 = buildUnsignedDivisionWithZeroCheck("U16", LlvmI16Type)
private val divideBy_s32 = buildSignedDivisionWithZeroCheck("S32", LlvmI32Type)
private val divideBy_u32 = buildUnsignedDivisionWithZeroCheck("U32", LlvmI32Type)
private val divideBy_s64 = buildSignedDivisionWithZeroCheck("S64", LlvmI64Type)
private val divideBy_u64 = buildUnsignedDivisionWithZeroCheck("U64", LlvmI64Type)
private val divideBy_sWord = buildSignedDivisionWithZeroCheck("SWord", EmergeWordType)
private val divideBy_uWord = buildUnsignedDivisionWithZeroCheck("UWord", EmergeWordType)

private fun <T : LlvmIntegerType> buildSignedCompareFn(
    emergeSignedTypeSimpleName: String,
    llvmType: T,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    val llvmSaturateSubIntrinsic = LlvmIntrinsic<T>(
        "llvm.ssub.sat.*",
        listOf(llvmType),
        listOf(llvmType, llvmType),
        llvmType,
    )

    return KotlinLlvmFunction.define(
        "emerge.core.${emergeSignedTypeSimpleName}::compareTo",
        llvmType,
    ) {
        instructionAliasAttributes()

        val lhs by param(llvmType)
        val rhs by param(llvmType)

        body {
            ret(
                call(llvmSaturateSubIntrinsic, listOf(lhs, rhs))
            )
        }
    }
}

private fun <T : LlvmIntegerType> buildUnsignedCompareFn(
    emergeUnsignedTypeSimpleName: String,
    llvmType: T,
    constantFactory: EmergeLlvmContext.(Long) -> LlvmValue<T>,
) : KotlinLlvmFunction<EmergeLlvmContext, T> {
    return KotlinLlvmFunction.define(
        "emerge.core.${emergeUnsignedTypeSimpleName}::compareTo",
        llvmType,
    ) {
        instructionAliasAttributes()

        val lhs by param(llvmType)
        val rhs by param(llvmType)

        body {
            conditionalBranch(
                condition = icmp(lhs, LlvmIntPredicate.EQUAL, rhs),
                ifTrue = {
                    ret(context.constantFactory(0))
                }
            )
            conditionalBranch(
                condition = icmp(lhs, LlvmIntPredicate.UNSIGNED_GREATER_THAN, rhs),
                ifTrue = {
                    ret(context.constantFactory(1))
                }
            )
            ret(context.constantFactory(-1))
        }
    }
}

private val compareTo_s8 = buildSignedCompareFn("S8", LlvmI8Type)
private val compareTo_u8 = buildUnsignedCompareFn("U8", LlvmI8Type) { i8(it.toByte()) }
private val compareTo_s16 = buildSignedCompareFn("S16", LlvmI16Type)
private val compareTo_u16 = buildUnsignedCompareFn("U16", LlvmI16Type) { i16(it.toShort()) }
private val compareTo_s32 = buildSignedCompareFn("S32", LlvmI32Type)
private val compareTo_u32 = buildUnsignedCompareFn("U32", LlvmI32Type) { i32(it.toInt()) }
private val compareTo_s64 = buildSignedCompareFn("S64", LlvmI64Type)
private val compareTo_u64 = buildUnsignedCompareFn("U64", LlvmI64Type) { i64(it) }
private val compareTo_sWord = buildSignedCompareFn("SWord", EmergeWordType)
private val compareTo_uWord = buildUnsignedCompareFn("UWord", EmergeWordType) { word(it) }

private fun buildSignedEnlargeTo64Fn(fromType: LlvmFixedIntegerType) = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI64Type>(
    "emerge.core.S${fromType.nBits}::toS64",
    LlvmI64Type,
) {
    instructionAliasAttributes()

    val self by param(fromType)

    body {
        ret(enlargeSigned(self, LlvmI64Type))
    }
}

private val convert_s8_to_s64 = buildSignedEnlargeTo64Fn(LlvmI8Type)
private val convert_s16_to_s64 = buildSignedEnlargeTo64Fn(LlvmI16Type)
private val convert_s32_to_s64 = buildSignedEnlargeTo64Fn(LlvmI32Type)

private fun buildUnsignedEnlargeTo64Fn(fromType: LlvmFixedIntegerType) = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI64Type>(
    "emerge.core.U${fromType.nBits}::toU64",
    LlvmI64Type,
) {
    instructionAliasAttributes()

    val self by param(fromType)

    body {
        ret(enlargeUnsigned(self, LlvmI64Type))
    }
}

private val convert_u8_to_u64 = buildUnsignedEnlargeTo64Fn(LlvmI8Type)
private val convert_u16_to_u64 = buildUnsignedEnlargeTo64Fn(LlvmI16Type)
private val convert_u32_to_u64 = buildUnsignedEnlargeTo64Fn(LlvmI32Type)