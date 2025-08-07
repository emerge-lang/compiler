package io.github.tmarsteel.emerge.backend.llvm.intrinsics.stdlib

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmS32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeSWordType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeUWordType
import io.github.tmarsteel.emerge.backend.llvm.linux.libcWriteFunction

internal val pureWrite = KotlinLlvmFunction.define<EmergeLlvmContext, EmergeSWordType>(
    "emerge.platform.pureWrite",
    EmergeSWordType,
) {
    val fd by param(LlvmS32Type)
    val bufPtr by param(pointerTo(LlvmVoidType))
    val len by param(EmergeUWordType)

    body {
        ret(
            call(context.libcWriteFunction, listOf(fd, bufPtr, len))
        )
    }
}