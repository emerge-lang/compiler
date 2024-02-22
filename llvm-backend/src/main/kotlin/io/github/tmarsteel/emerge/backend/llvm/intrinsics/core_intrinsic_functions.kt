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

internal val nullWeakReferences = KotlinLlvmFunction.define<LlvmContext, _>("emerge.platform.nullWeakReferences", LlvmVoidType) {
    val self by param(PointerToAnyEmergeValue)
    body {
        // TODO: implement!
        retVoid()
    }
}

internal val getSupertypePointers = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.platform.getSupertypePointers",
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

        arrayPointer.afterReferenceCreated()
        return@body ret(arrayPointer)
    }
}

context(BasicBlockBuilder<*, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.afterReferenceCreated() {
    val referenceCountPtr = this.anyValueBase().member { strongReferenceCount }.get()

    store(
        add(referenceCountPtr.dereference(), context.word(1)),
        referenceCountPtr,
    )
}

private val dropReferenceFunction = KotlinLlvmFunction.define<LlvmContext, _>(
    "emerge.platform.dropReference",
    LlvmVoidType
) {
    val objectPtr by param(PointerToAnyEmergeValue)
    body {
        val referenceCountPtr = getelementptr(objectPtr).member { EmergeHeapAllocatedValueBaseType.strongReferenceCount }.get()
        val decremented = sub(referenceCountPtr.dereference(), context.word(1))
        val isZero = icmp(decremented, IntegerComparison.EQUAL, context.word(0))
        conditionalBranch(isZero, ifTrue = {
            call(nullWeakReferences.getInContext(context), listOf(objectPtr))
            val typeinfoPtr = getelementptr(objectPtr)
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

        retVoid()
    }
}

context(BasicBlockBuilder<*, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.afterReferenceDropped() {
    call(dropReferenceFunction.getInContext(context), listOf(this@afterReferenceDropped))
}