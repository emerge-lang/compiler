package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType

internal val valueArrayFinalize = KotlinLlvmFunction.define<EmergeLlvmContext, _>("valuearray_finalize", LlvmVoidType) {
    param(PointerToAnyValue)
    body {
        // nothing to do. There are no references, just values, so no dropping needed
        retVoid()
    }
}

internal val nullWeakReferences = KotlinLlvmFunction.define<EmergeLlvmContext, _>("nullWeakReferences", LlvmVoidType) {
    val self by param(PointerToAnyValue)
    body {
        // TODO: implement!
        retVoid()
    }
}