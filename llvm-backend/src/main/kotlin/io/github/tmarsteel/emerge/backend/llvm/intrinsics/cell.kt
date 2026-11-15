package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member

internal val cellGetFunction = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Cell::value",
    PointerToAnyEmergeValue,
) {
    val self by param(PointerToAnyEmergeValue)

    body {
        val valueField = context.cellType.irClass.fieldOfMemberVariable("_value")
        val selfAsCell = self.reinterpretAs(pointerTo(context.cellType))
        val valueFieldPtr = getelementptr(selfAsCell)
            .member(valueField)
            .get()
            .reinterpretAs(pointerTo(PointerToAnyEmergeValue))

        val value = valueFieldPtr.dereference()
        value.afterReferenceCreated(valueField.type)
        ret(value)
    }
}

internal val cellSetFunction = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Cell::update",
    LlvmVoidType,
) {
    val self by param(PointerToAnyEmergeValue)
    val newValue by param(PointerToAnyEmergeValue)

    body {
        val valueField = context.cellType.irClass.fieldOfMemberVariable("_value")
        val selfAsCell = self.reinterpretAs(pointerTo(context.cellType))
        val valueFieldPtr = getelementptr(selfAsCell)
            .member(valueField)
            .get()
            .reinterpretAs(pointerTo(PointerToAnyEmergeValue))

        val previousValue = valueFieldPtr.dereference("previous")
        previousValue.afterReferenceDropped(valueField.type)
        newValue.afterReferenceCreated(valueField.type)
        store(newValue, valueFieldPtr)

        retVoid()
    }
}