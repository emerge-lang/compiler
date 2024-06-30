package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext

val isNullBuiltin = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmBooleanType>("emerge.core.isNull", LlvmBooleanType) {
    val value by param(pointerTo(LlvmVoidType))

    instructionAliasAttributes()

    body {
        ret(isNull(value))
    }
}