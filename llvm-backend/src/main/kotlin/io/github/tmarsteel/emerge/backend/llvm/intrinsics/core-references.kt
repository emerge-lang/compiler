package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue

internal val getSupertypePointers = KotlinLlvmFunction.define<LlvmContext, _>(
    "getSupertypePointers",
    pointerTo(EmergeArrayOfPointersToTypeInfoType),
) {
    val inputRef by param(PointerToAnyValue)
    body {
        val typeinfoPointer = getelementptr(inputRef)
            .member { typeinfo }
            .get()
            .dereference()
        val arrayPointer = getelementptr(typeinfoPointer)
            .member { supertypes }
            .get()
            .dereference()

        arrayPointer.incrementStrongReferenceCount()
        return@body ret(arrayPointer)
    }
}

context(BasicBlockBuilder<*, *>)
internal fun LlvmValue<LlvmPointerType<out ArrayType<*>>>.incrementStrongReferenceCount() {
    val referenceCountPtr = getelementptr(this@incrementStrongReferenceCount)
        .member { base }
        .member { anyBase }
        .member { strongReferenceCount }
        .get()

    store(
        add(referenceCountPtr.dereference(), word(1)),
        referenceCountPtr,
    )
}