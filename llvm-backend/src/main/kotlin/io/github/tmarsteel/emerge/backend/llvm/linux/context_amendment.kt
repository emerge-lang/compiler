package io.github.tmarsteel.emerge.backend.llvm.linux

import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeWordType
import io.github.tmarsteel.emerge.backend.llvm.tackLazyVal

/**
 * The libc write function, if available on this target
 */
internal val EmergeLlvmContext.libcWriteFunction: LlvmFunction<EmergeWordType> by tackLazyVal {
    LlvmFunction(
        getNamedFunctionAddress("write")!!,
        LlvmFunctionType(
            EmergeWordType,
            listOf(
                LlvmI32Type,
                LlvmPointerType.pointerTo(LlvmVoidType),
                EmergeWordType
            )
        )
    )
}