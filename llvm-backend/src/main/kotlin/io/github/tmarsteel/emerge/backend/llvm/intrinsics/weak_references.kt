package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction.Companion.callIntrinsic
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.fallibleSuccess

/*
An emerge.core.Weak referring to an array cannot refer to the emerge.platform.ArrayBox it receives: that box
usually only exists for the duration of the call to the constructor of Weak. Instead, the Weak holds its own
box, a "weak array box": it has the layout of an ArrayBox, but doesn't hold a reference to the array object. The
base pointer of its slice is registered as a weak reference to the array object instead.
 */

private val weakArrayBoxFinalizer = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.platform.weakArrayBox_finalize",
    LlvmVoidType,
) {
    val self by param(PointerToAnyEmergeValue)
    body {
        // only the weak reference owns the box, and that frees it on its own
        inlinePanic("weak array box was finalized through reference counting")
    }
}

private val weakArrayBoxTypeinfo = StaticAndDynamicTypeInfo.defineRaw(
    { _ -> "emerge.platform.WeakArrayBox" },
    emptyList(),
    { ctx -> ctx.registerIntrinsic(weakArrayBoxFinalizer) },
    { emptyMap() },
)

context(BasicBlockBuilder<EmergeLlvmContext, *>)
private fun hasTypeinfo(obj: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>, typeinfo: StaticAndDynamicTypeInfo): LlvmValue<LlvmBooleanType> {
    val typeinfoPtr = obj
        .anyValueBase()
        .member { this.typeinfo }
        .get()
        .dereference()
    return isEq(typeinfoPtr, typeinfo.dynamic)
}

context(BasicBlockBuilder<EmergeLlvmContext, *>)
private fun pointerToBoxedSlice(box: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>): LlvmValue<LlvmPointerType<EmergeArraySliceType>> {
    val boxType = context.boxTypeArray
    return getelementptr(box.reinterpretAs(pointerTo(boxType)))
        .member(boxType.irClass.fields.single())
        .get()
        .reinterpretAs(pointerTo(EmergeArraySliceType))
}

context(BasicBlockBuilder<EmergeLlvmContext, *>)
private fun pointerToBoxedSliceBase(box: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>): LlvmValue<LlvmPointerType<LlvmPointerType<out EmergeHeapAllocated>>> {
    return getelementptr(pointerToBoxedSlice(box))
        .member { base }
        .get()
        .reinterpretAs(pointerTo(PointerToAnyEmergeValue))
}

/**
 * Like [registerWeakReference], but for a [objectBeingReferred] that is an `emerge.platform.ArrayBox`, replaces
 * the value at [pointerToWeakReference] with a weak array box.
 */
internal val registerWeakReferenceToAnyValue = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.platform.registerWeakReferenceToAnyValue",
    LlvmVoidType,
) {
    val pointerToWeakReference by param(pointerTo(PointerToAnyEmergeValue))
    val objectBeingReferred by param(PointerToAnyEmergeValue)
    body {
        conditionalBranch(
            condition = hasTypeinfo(objectBeingReferred, context.boxTypeArray.getTypeinfoInContext(context)),
            ifTrue = {
                val weakBox = heapAllocate(context.boxTypeArray)
                store(context.word(1), weakBox.anyValueBase().member { strongReferenceCount }.get())
                store(weakArrayBoxTypeinfo.provide(context).dynamic, weakBox.anyValueBase().member { typeinfo }.get())
                store(pointerToBoxedSlice(objectBeingReferred).dereference(), pointerToBoxedSlice(weakBox))
                store(weakBox.reinterpretAs(PointerToAnyEmergeValue), pointerToWeakReference)

                val baseSlot = pointerToBoxedSliceBase(weakBox)
                callIntrinsic(registerWeakReference, listOf(baseSlot, baseSlot.dereference()))
                retVoid()
            }
        )

        callIntrinsic(registerWeakReference, listOf(pointerToWeakReference, objectBeingReferred))
        retVoid()
    }
}

/**
 * Like [unregisterWeakReference], undoes [registerWeakReferenceToAnyValue].
 */
internal val unregisterWeakReferenceToAnyValue = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.platform.unregisterWeakReferenceToAnyValue",
    LlvmVoidType,
) {
    val pointerToWeakReference by param(pointerTo(PointerToAnyEmergeValue))
    val objectBeingReferred by param(PointerToAnyEmergeValue)
    body {
        conditionalBranch(condition = isNull(objectBeingReferred), ifTrue = {
            retVoid()
        })
        conditionalBranch(
            condition = hasTypeinfo(objectBeingReferred, weakArrayBoxTypeinfo.provide(context)),
            ifTrue = {
                val baseSlot = pointerToBoxedSliceBase(objectBeingReferred)
                callIntrinsic(unregisterWeakReference, listOf(baseSlot, baseSlot.dereference()))
                call(context.freeFunction, listOf(objectBeingReferred))
                retVoid()
            }
        )

        callIntrinsic(unregisterWeakReference, listOf(pointerToWeakReference, objectBeingReferred))
        retVoid()
    }
}

/** implementation of `emerge.core.Weak::toStrongOrNull` */
internal val weakToStrongOrNull = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Weak::toStrongOrNull",
    EmergeFallibleCallResult.ofEmergeReference,
) {
    val self by param(PointerToAnyEmergeValue)
    body {
        val weakType = context.weakType
        val referred = getelementptr(self.reinterpretAs(pointerTo(weakType)))
            .member(weakType.irClass.fields.single())
            .get()
            .dereference()
            .reinterpretAs(PointerToAnyEmergeValue)

        conditionalBranch(condition = isNull(referred), ifTrue = {
            ret(fallibleSuccess(referred))
        })
        conditionalBranch(
            condition = hasTypeinfo(referred, weakArrayBoxTypeinfo.provide(context)),
            ifTrue = {
                val slice = pointerToBoxedSlice(referred).dereference()
                conditionalBranch(condition = isNull(slice.sliceBase), ifTrue = {
                    ret(fallibleSuccess(context.nullValue(PointerToAnyEmergeValue)))
                })
                // the box constructor creates the reference to the array object
                ret(
                    call(context.boxTypeArray.constructor, listOf(slice))
                        .reinterpretAs(EmergeFallibleCallResult.ofEmergeReference)
                )
            }
        )

        referred.afterReferenceCreated(isNullable = false)
        ret(fallibleSuccess(referred))
    }
}
