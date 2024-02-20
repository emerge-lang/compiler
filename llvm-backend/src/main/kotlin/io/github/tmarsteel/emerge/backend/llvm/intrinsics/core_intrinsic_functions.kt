package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.IntegerComparison
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType

internal val nullWeakReferences = KotlinLlvmFunction.define<LlvmContext, _>("nullWeakReferences", LlvmVoidType) {
    val self by param(PointerToAnyEmergeValue)
    body {
        // TODO: implement!
        retVoid()
    }
}

internal val getSupertypePointers = KotlinLlvmFunction.define<LlvmContext, _>(
    "getSupertypePointers",
    PointerToEmergeArrayOfPointersToTypeInfoType,
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
            .member { finalizeFunction }
            .get()
            .dereference()

        call(finalizerFn, EmergeAnyValueVirtualsType.finalizeFunctionType, emptyList())

        concludeBranch()
    }, ifFalse = {
        store(decremented, referenceCountPtr)
        concludeBranch()
    })
}