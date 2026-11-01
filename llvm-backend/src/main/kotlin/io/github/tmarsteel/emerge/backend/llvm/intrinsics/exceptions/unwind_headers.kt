package io.github.tmarsteel.emerge.backend.llvm.intrinsics.exceptions

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeUWordType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.uWord

internal val unwindContextSize = KotlinLlvmFunction.define<EmergeLlvmContext, EmergeUWordType>(
    "emerge.platform.unwind_context_size",
    EmergeUWordType,
) {
    body {
        when (context.target.triple) {
            "x86_64-pc-linux-gnu" -> {
                /*
                from libunwind headers:
                libunwind-x86_64.h: On x86_64, we can directly use ucontext_t as the unwind context
                libunwind-x86_64.h: typedef ucontext_t unw_tdep_context_t;

                running on this target: sprintf("%lu", sizeof(ucontext_t)) prints 968
                */
                ret(context.uWord(968u))
            }
            else -> throw CodeGenerationException("unsupported target")
        }
    }
}

internal val unwindCursorSize = KotlinLlvmFunction.define<EmergeLlvmContext, EmergeUWordType>(
    "emerge.platform.unwind_cursor_size",
    EmergeUWordType,
) {
    body {
        when (context.target.triple) {
            "x86_64-pc-linux-gnu" -> {
                /*
                from libunwind headers:
                unw_word_t is uint64_t
                UNW_TDEP_CURSOR_LEN is 127
                */
                ret(context.uWord(127u * 8u))
            }
            else -> throw CodeGenerationException("unsupported target")
        }
    }
}