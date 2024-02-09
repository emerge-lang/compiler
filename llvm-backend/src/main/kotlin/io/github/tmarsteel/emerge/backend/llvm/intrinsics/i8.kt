package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmStructType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType

internal object I8BoxType : LlvmStructType("box_i8") {
    val base by structMember(AnyValueType)
    val value by structMember(LlvmI8Type)
}

internal val I8BoxConstructor = KotlinLlvmFunction.define<EmergeLlvmContext, _>("box_i8_constructor", pointerTo(I8BoxType)) {
    TODO()
}

internal val I8BoxGetElement: KotlinLlvmFunction<EmergeLlvmContext, LlvmPointerType<I8BoxType>> = KotlinLlvmFunction.define(
    "valuearray_i8_get_boxed",
    pointerTo(I8BoxType)
) {
    val self by param(pointerTo(ValueArrayI8Type))
    val index by param(LlvmWordType)
    body {
        // TODO: bounds check!
        val raw = getelementptr(self)
            .member { elements }
            .index(index)
            .get()
            .dereference()

        val ctor = I8BoxConstructor.getInContext(context)
        ret(call(ctor, listOf(raw)))
    }
}

internal val I8BoxSetElement: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> = KotlinLlvmFunction.define(
    "valuearray_i8_set_boxed",
    LlvmVoidType
) {
    val self by param(pointerTo(ValueArrayI8Type))
    val index by param(LlvmWordType)
    val valueBox by param(pointerTo(I8BoxType))
    body {
        // TODO: bounds check!
        val raw = getelementptr(valueBox)
            .member { value }
            .get()
            .dereference()
        val targetPointer = getelementptr(self)
            .member { elements }
            .index(index)
            .get()

        store(raw, targetPointer)
        retVoid()
    }
}

internal val ValueArrayI8Type = ArrayType(
    LlvmI8Type,
    StaticAndDynamicTypeInfo.define(
        "array_i8",
        emptyList(),
        valueArrayFinalize,
    ) {
        listOf(
            word(ArrayType.VIRTUAL_FUNCTION_HASH_GET_ELEMENT) to I8BoxGetElement,
            word(ArrayType.VIRTUAL_FUNCTION_HASH_SET_ELEMENT) to I8BoxSetElement,
        )
    }
)