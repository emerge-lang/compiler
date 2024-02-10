package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32

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

internal val arrayIndexOfFirst = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.ffi.c.addressOfFirst",
    pointerTo(LlvmVoidType),
) {
    val arrayPointer by param(pointerTo(EmergeReferenceArrayType))
    body {
        val ptr = getelementptr(arrayPointer, context.i32(1))
            .get()
            .reinterpretAs(pointerTo(LlvmVoidType))

        ret(ptr)
    }
}

internal val arraySize = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.core.size",
    LlvmWordType,
) {
    val arrayPointer by param(pointerTo(EmergeReferenceArrayType))
    body {
        ret(
            getelementptr(arrayPointer)
                .member { base }
                .member { elementCount }
                .get()
                .dereference()
        )
    }
}

context(BasicBlockBuilder<*, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.incrementStrongReferenceCount() {
    val referenceCountPtr = this.anyValueBase().member { strongReferenceCount }.get()

    store(
        add(referenceCountPtr.dereference(), context.word(1)),
        referenceCountPtr,
    )
}