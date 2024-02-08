package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType

internal val EmergeReferenceArrayType: ArrayType<LlvmPointerType<AnyValueType>> = ArrayType(PointerToAnyValue, "ref") { context -> StaticAndDynamicTypeInfo.buildInContext(
    context,
    "array_ref",
    emptyList(),
    refArrayFinalize,
    listOf(
        context.word(ArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT) to I8BoxGetElement,
        context.word(ArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT) to I8BoxSetElement,
    )
) }

private val refArrayFinalize: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "refarray_finalize",
    LlvmVoidType,
) {
    val self by param(PointerToAnyValue)
    body {
        // TODO: walk references, drop each properly
        retVoid()
    }
}