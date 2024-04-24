package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.IntegerComparison
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.llvmValueType

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
        val arrayPointerAsAny = getelementptr(typeinfoPointer)
            .member { supertypes }
            .get()
            .dereference()

        /** see [TypeinfoType.supertypes] for why this cast is needed */
        val arrayPointer = arrayPointerAsAny
            .reinterpretAs(PointerToEmergeArrayOfPointersToTypeInfoType)

        // refcounting not needed, typeinfo is always static
        ret(arrayPointer)
    }
}

// TODO: mark with alwaysinline
private val afterReferenceCreatedNonNullable = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.platform.afterReferenceCreatedNonNullable",
    LlvmVoidType,
) {
    val inputRef by param(PointerToAnyEmergeValue)
    body {
        val referenceCountPtr = getelementptr(inputRef).member { strongReferenceCount }.get()

        store(
            add(referenceCountPtr.dereference(), context.word(1)),
            referenceCountPtr,
        )
        retVoid()
    }
}

private val afterReferenceCreatedNullable = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.platform.afterReferenceCreatedNullable",
    LlvmVoidType,
) {
    val inputRef by param(PointerToAnyEmergeValue)
    body {
        conditionalBranch(not(isNull(inputRef)), ifTrue = {
            call(context.registerIntrinsic(afterReferenceCreatedNonNullable), listOf(inputRef))
            concludeBranch()
        })
        retVoid()
    }
}

/**
 * @param isNullable whether, according to the type information given by the frontend ([IrType.isNullable]),
 * the reference is nullable. If true, a runtime null-check will be emitted.
 */
context(BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.afterReferenceCreated(
    isNullable: Boolean,
) {
    if (isNullable) {
        call(context.registerIntrinsic(afterReferenceCreatedNullable), listOf(this))
    } else {
        call(context.registerIntrinsic(afterReferenceCreatedNonNullable), listOf(this))
    }
}

/**
 * A no-op iff the [emergeType] is a value-type.
 *
 * Otherwise, increments the reference counter, potentially guarded by a null-check if [IrType.isNullable]
 * is `true`.
 */
context(BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun LlvmValue<out LlvmType>.afterReferenceCreated(
    emergeType: IrType,
) {
    if (emergeType.llvmValueType != null || type == LlvmVoidType) {
        return
    }

    val asAnyRef = reinterpretAs(PointerToAnyEmergeValue)
    asAnyRef.afterReferenceCreated(emergeType.isNullable)
}

// TODO for exceptions: add dropReferenceInCatch(ref: Any, throwable: Throwable)
private val dropReferenceFunction = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.platform.dropReference",
    LlvmVoidType
) {
    val objectPtr by param(PointerToAnyEmergeValue)
    body {
        val referenceCountPtr = getelementptr(objectPtr).member { EmergeHeapAllocatedValueBaseType.strongReferenceCount }.get()
        val decremented = sub(referenceCountPtr.dereference(), context.word(1))
        val isZero = icmp(decremented, IntegerComparison.EQUAL, context.word(0))
        conditionalBranch(isZero, ifTrue = {
            call(context.registerIntrinsic(nullWeakReferences), listOf(objectPtr))
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

/**
 * @param isNullable whether, according to the type information given by the frontend ([IrType.isNullable]),
 * the reference is nullable. If true, a runtime null-check will be emitted.
 */
context(BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.afterReferenceDropped(
    isNullable: Boolean,
) {
    if (isNullable) {
        conditionalBranch(condition = not(isNull(this)), ifTrue = {
            call(context.registerIntrinsic(dropReferenceFunction), listOf(this@afterReferenceDropped))
            concludeBranch()
        })
        return
    }

    call(context.registerIntrinsic(dropReferenceFunction), listOf(this@afterReferenceDropped))
}

/**
 * A no-op iff the [emergeType] is a value-type.
 *
 * Otherwise, emits a call to [dropReferenceFunction], potentially guarded by a null-check if [IrType.isNullable]
 * is `true`.
 */
context(BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun LlvmValue<out LlvmType>.afterReferenceDropped(
    emergeType: IrType,
) {
    if (emergeType.llvmValueType != null || type == LlvmVoidType) {
        return
    }

    this.reinterpretAs(PointerToAnyEmergeValue).afterReferenceDropped(emergeType.isNullable)
}