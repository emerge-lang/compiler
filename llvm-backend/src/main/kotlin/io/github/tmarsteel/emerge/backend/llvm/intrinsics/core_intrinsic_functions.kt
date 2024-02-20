package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.IntegerComparison
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32

internal val valueArrayFinalize = KotlinLlvmFunction.define<LlvmContext, _>("valuearray_finalize", LlvmVoidType) {
    param(PointerToAnyEmergeValue)
    body {
        // nothing to do. There are no references, just values, so no dropping needed
        retVoid()
    }
}

internal val nullWeakReferences = KotlinLlvmFunction.define<LlvmContext, _>("nullWeakReferences", LlvmVoidType) {
    val self by param(PointerToAnyEmergeValue)
    body {
        // TODO: implement!
        retVoid()
    }
}

internal val getSupertypePointers = KotlinLlvmFunction.define<LlvmContext, _>(
    "getSupertypePointers",
    pointerTo(EmergeArrayOfPointersToTypeInfoType),
) {
    val inputRef by param(PointerToAnyEmergeValue)
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

/* TODO: refactor to addressOf(index: uword)
   that would be easy to do for concrete types; but there should be an overload for Array<out Any>
   and with the currently planned rules for overloading, having an addressOf(self: Array<out Any>)
   would prevent declaring a specialized addressOf(self: Array<Byte>) etc.

   other possibility: arrays always as slices. Right now array references are a single ptr to the array
   object on the heap. Array references could become fat pointers consisting of
   1. a pointer to the array object on the heap, for reference counting
   2. the number of elements being referenced
   3. a pointer to the first element being referenced, null when <num of elements referenced> == 0
   Then, when you need the address of any other array element other than the first, you can create a slice
   of the array (e.g. someArray.subArray(2, someArray.length)) and then do addressOfFirst
 */
internal val arrayAddressOfFirst = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.ffi.c.addressOfFirst",
    pointerTo(LlvmVoidType),
) {
    val arrayPointer by param(pointerTo(EmergeArrayBaseType))
    body {
        val ptr = getelementptr(arrayPointer, context.i32(1))
            .get()
            .reinterpretAs(pointerTo(LlvmVoidType))

        ret(ptr)
    }
}

internal val arraySize = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.core.size",
    EmergeWordType,
) {
    val arrayPointer by param(pointerTo(EmergeArrayBaseType))
    body {
        ret(
            getelementptr(arrayPointer)
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

context(BasicBlockBuilder<*, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.decrementStrongReferenceCount() {
    val referenceCountPtr = this.anyValueBase().member { strongReferenceCount }.get()
    val decremented = sub(referenceCountPtr.dereference(), context.word(1))
    val isZero = icmp(decremented, IntegerComparison.EQUAL, context.word(0))
    conditionalBranch(isZero, ifTrue = {
        call(nullWeakReferences.getInContext(context), listOf(this@decrementStrongReferenceCount))
        val typeinfoPtr = this@decrementStrongReferenceCount.anyValueBase()
            .member { typeinfo }
            .get()
            .dereference()
        val finalizerFn = getelementptr(typeinfoPtr)
            .member { anyValueVirtuals }
            .member { dropFunction }
            .get()
            .dereference()

        call(finalizerFn, EmergeAnyValueVirtualsType.dropFunctionType, emptyList())

        concludeBranch()
    }, ifFalse = {
        store(decremented, referenceCountPtr)
        concludeBranch()
    })
}