package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI16Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI64Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
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

internal val unaryMinus_s8 = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI8Type>(
    "emerge.core.S8::unaryMinus",
    LlvmI8Type,
) {
    instructionAliasAttributes()

    val self by param(LlvmI8Type)

    body {
        ret(sub(context.i8(0), self))
    }
}

internal val unaryMinus_s16 = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI16Type>(
    "emerge.core.S16::unaryMinus",
    LlvmI16Type,
) {
    instructionAliasAttributes()

    val self by param(LlvmI16Type)

    body {
        ret(sub(context.i16(0), self))
    }
}

internal val unaryMinus_s32 = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI32Type>(
    "emerge.core.S32::unaryMinus",
    LlvmI32Type,
) {
    instructionAliasAttributes()

    val self by param(LlvmI32Type)

    body {
        ret(sub(context.i32(0), self))
    }
}

internal val unaryMinus_s64 = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI64Type>(
    "emerge.core.S64::unaryMinus",
    LlvmI64Type,
) {
    instructionAliasAttributes()

    val self by param(LlvmI64Type)

    body {
        ret(sub(context.i64(0), self))
    }
}

internal val unaryMinus_sWord = KotlinLlvmFunction.define<EmergeLlvmContext, EmergeWordType>(
    "emerge.core.SWord::unaryMinus",
    EmergeWordType,
) {
    instructionAliasAttributes()

    val self by param(EmergeWordType)

    body {
        ret(sub(context.word(0), self))
    }
}

internal val negate_s8 = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI8Type>(
    "emerge.core.S8::negate",
    LlvmI8Type,
) {
    instructionAliasAttributes()

    val self by param(LlvmI8Type)

    body {
        ret(not(self))
    }
}

internal val negate_u8 = negate_s8.createAlias("emerge.core.U8::negate")

internal val negate_s16 = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI16Type>(
    "emerge.core.S16::negate",
    LlvmI16Type,
) {
    instructionAliasAttributes()

    val self by param(LlvmI16Type)

    body {
        ret(not(self))
    }
}

internal val negate_u16 = negate_s16.createAlias("emerge.core.U16::negate")

internal val negate_s32 = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI32Type>(
    "emerge.core.S32::negate",
    LlvmI32Type,
) {
    instructionAliasAttributes()

    val self by param(LlvmI32Type)

    body {
        ret(not(self))
    }
}

internal val negate_u32 = negate_s32.createAlias("emerge.core.U32::negate")

internal val negate_s64 = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmI64Type>(
    "emerge.core.S64::negate",
    LlvmI64Type,
) {
    instructionAliasAttributes()

    val self by param(LlvmI64Type)

    body {
        ret(not(self))
    }
}

internal val negate_u64 = negate_s64.createAlias("emerge.core.U64::negate")

internal val negate_sWord = KotlinLlvmFunction.define<EmergeLlvmContext, EmergeWordType>(
    "emerge.core.SWord::negate",
    EmergeWordType,
) {
    instructionAliasAttributes()

    val self by param(EmergeWordType)

    body {
        ret(not(self))
    }
}

internal val negate_uWord = negate_sWord.createAlias("emerge.core.UWord::negate")