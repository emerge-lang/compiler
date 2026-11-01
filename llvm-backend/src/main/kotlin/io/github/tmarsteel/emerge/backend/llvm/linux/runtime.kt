package io.github.tmarsteel.emerge.backend.llvm.linux

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction.Companion.callIntrinsic
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.s32
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.abortOnException
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.panicOnThrowable

val EmergeEntrypoint = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>("main", LlvmVoidType) {
    body {
        callIntrinsic(context.globalInitializerFn, emptyList())
        val threadInitResult = callIntrinsic(context.threadInitializerFn, emptyList())
        threadInitResult.abortOnException { exceptionPtr ->
            callIntrinsic(panicOnThrowable, listOf(exceptionPtr))
            unreachable()
        }
        val mainResult = call(context.mainFunction, emptyList())
        if (mainResult.type is EmergeFallibleCallResult<*>) {
            (mainResult as LlvmValue<EmergeFallibleCallResult<LlvmType>>).abortOnException { exceptionPtr ->
                callIntrinsic(panicOnThrowable, listOf(exceptionPtr))
                unreachable()
            }
        }

        call(context.exitFunction, listOf(context.s32(0)))
        retVoid()
    }
}

