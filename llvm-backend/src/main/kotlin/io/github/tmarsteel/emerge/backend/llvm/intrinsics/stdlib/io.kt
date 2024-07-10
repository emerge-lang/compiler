package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.linux.libcWriteFunction

internal val pureWrite = KotlinLlvmFunction.define<EmergeLlvmContext, EmergeWordType>(
    "emerge.platform.pureWrite",
    EmergeWordType,
) {
    val fd by param(LlvmI32Type)
    val bufPtr by param(pointerTo(LlvmVoidType))
    val len by param(EmergeWordType)

    body {
        ret(
            call(context.libcWriteFunction, listOf(fd, bufPtr, len))
        )
    }
}