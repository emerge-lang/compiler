package io.github.tmarsteel.emerge.backend.llvm.linux

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeLlvmContext

val EmergeEntrypoint = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>("main", LlvmVoidType) {
    body {
        call(context.registerIntrinsic(context.threadInitializerFn), emptyList())
        call(context.mainFunction, emptyList())
        call(context.exitFunction, listOf(context.i32(0)))
        retVoid()
    }
}

