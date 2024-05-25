package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.ir.IrType
import io.github.tmarsteel.emerge.backend.llvm.autoboxer
import io.github.tmarsteel.emerge.backend.llvm.codegen.sizeof
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction.Companion.callIntrinsic
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmConstant
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAddressType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.jna.Llvm
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode

internal val nullWeakReferences = KotlinLlvmFunction.define<EmergeLlvmContext, _>("emerge.platform.nullWeakReferences", LlvmVoidType) {
    val self by param(PointerToAnyEmergeValue)
    body {
        val weakRefCollPtrPtr = getelementptr(self)
            .member { weakReferenceCollection }
            .get()
        val weakRefCollPtr = weakRefCollPtrPtr.dereference()
        store(context.nullValue(pointerTo(EmergeWeakReferenceCollectionType)), weakRefCollPtrPtr)
        conditionalBranch(
            condition = isNotNull(weakRefCollPtr),
            ifTrue = {
                callIntrinsic(nullAndFreeWeakReferenceCollection, listOf(weakRefCollPtr))
                concludeBranch()
            }
        )
        retVoid()
    }
}

private val nullAndFreeWeakReferenceCollection: KotlinLlvmFunction<EmergeLlvmContext, LlvmVoidType> by lazy {
    KotlinLlvmFunction.define("emerge.platform.nullAndFreeWeakReferenceCollection", LlvmVoidType) {
        val collectionPtr by param(pointerTo(EmergeWeakReferenceCollectionType))
        body {
            val currentColIndexPtr = alloca(EmergeWordType)
            store(context.word(0), currentColIndexPtr)
            val nextCollPtr = getelementptr(collectionPtr)
                .member { next }
                .get()
                .dereference()
            conditionalBranch(
                condition = isNotNull(nextCollPtr),
                ifTrue = {
                    callIntrinsic(nullAndFreeWeakReferenceCollection, listOf(nextCollPtr))
                    concludeBranch()
                }
            )
            loop(
                header = {
                    conditionalBranch(
                        condition = icmp(currentColIndexPtr.dereference(), LlvmIntPredicate.EQUAL, context.word(EmergeWeakReferenceCollectionType.pointersToWeakReferences.type.elementCount)),
                        ifTrue = {
                            breakLoop()
                        }
                    )
                    doIteration()
                },
                body = {
                    val currentColIndex = currentColIndexPtr.dereference()
                    val referringReferencePtrPtr = getelementptr(collectionPtr)
                        .member { pointersToWeakReferences }
                        .index(currentColIndex)
                        .get()
                    val referringReferencePtr = referringReferencePtrPtr.dereference()
                    conditionalBranch(condition = isNotNull(referringReferencePtr), ifTrue = {
                        store(context.nullValue(PointerToAnyEmergeValue), referringReferencePtr)
                        store(context.nullValue(pointerTo(PointerToAnyEmergeValue)), referringReferencePtrPtr)
                        concludeBranch()
                    })
                    store(add(currentColIndex, context.word(1)), currentColIndexPtr)
                    loopContinue()
                }
            )
            call(context.freeFunction, listOf(collectionPtr))
            retVoid()
        }
    }
}

/**
 * @param pointerToWeakReference points to the word-sized location in memory where the address of [objectBeingReferred]
 * is stored
 * @param objectBeingReferred a pointer to the object to which a weak reference exists
 */
internal val registerWeakReference = KotlinLlvmFunction.define<EmergeLlvmContext, _>("emerge.platform.registerWeakReference", LlvmVoidType) {
    val pointerToWeakReference by param(pointerTo(PointerToAnyEmergeValue))
    val objectBeingReferred by param(PointerToAnyEmergeValue)
    body registerWeakRefFn@{
        val currentWeakRefCollPtrPtrPtr = alloca(pointerTo(pointerTo(EmergeWeakReferenceCollectionType)))
        val currentCollIndexPtr = alloca(EmergeWordType)
        store(
            getelementptr(objectBeingReferred)
                .member { weakReferenceCollection }
                .get(),
            to = currentWeakRefCollPtrPtrPtr,
        )
        loop(
            header = {
                conditionalBranch(
                    condition = isNull(currentWeakRefCollPtrPtrPtr.dereference().dereference()),
                    ifTrue = {
                        breakLoop()
                    }
                )
                doIteration()
            },
            body = collIterBody@{
                store(context.word(0), to = currentCollIndexPtr)
                loop(
                    header = innerHeader@{
                        conditionalBranch(
                            condition = icmp(currentCollIndexPtr.dereference(), LlvmIntPredicate.EQUAL, context.word(EmergeWeakReferenceCollectionType.pointersToWeakReferences.type.elementCount)),
                            ifTrue = {
                                this@innerHeader.breakLoop()
                            }
                        )
                        this@innerHeader.doIteration()
                    },
                    body = collEntryIterBody@{
                        val currentColIndexValue = currentCollIndexPtr.dereference()
                        val entryPtr = getelementptr(currentWeakRefCollPtrPtrPtr.dereference().dereference())
                            .member { pointersToWeakReferences }
                            .index(currentColIndexValue)
                            .get()
                        val entryValue = entryPtr.dereference()
                        conditionalBranch(
                            condition = isNull(entryValue),
                            ifTrue = {
                                store(pointerToWeakReference, to = entryPtr)
                                retVoid()
                            }
                        )
                        store(
                            add(currentColIndexValue, context.word(1)),
                            to = currentCollIndexPtr
                        )
                        this@collEntryIterBody.loopContinue()
                    }
                )
                // the current collection doesn't have any free slots, try the next
                val nextCollPtrPtr = getelementptr(currentWeakRefCollPtrPtrPtr.dereference().dereference())
                    .member { next }
                    .get()
                store(nextCollPtrPtr, to = currentWeakRefCollPtrPtrPtr)
                this@collIterBody.loopContinue()
            }
        )
        // all collections are filled, allocate a new one
        val newCollPtr = heapAllocate(EmergeWeakReferenceCollectionType)
        memset(newCollPtr, context.i8(0), EmergeWeakReferenceCollectionType.sizeof())
        store(
            pointerToWeakReference,
            to = getelementptr(newCollPtr)
                .member { pointersToWeakReferences }
                .index(context.word(0))
                .get()
        )
        store(newCollPtr, to = currentWeakRefCollPtrPtrPtr.dereference())
        retVoid()
    }
}

internal val unregisterWeakReference = KotlinLlvmFunction.define<LlvmContext, _>("emerge.platform.unregisterWeakReference", LlvmVoidType) {
    val pointerToWeakReference by param(pointerTo(PointerToAnyEmergeValue))
    val objectBeingReferred by param(PointerToAnyEmergeValue)
    body {
        conditionalBranch(condition = isNull(objectBeingReferred), ifTrue = {
            // the weak reference is already gone -> nothing to do
            retVoid()
        })
        val currentWeakRefCollPtrPtrPtr = alloca(pointerTo(pointerTo(EmergeWeakReferenceCollectionType)))
        val currentCollIndexPtr = alloca(EmergeWordType)
        store(
            getelementptr(objectBeingReferred)
                .member { weakReferenceCollection }
                .get(),
            to = currentWeakRefCollPtrPtrPtr,
        )
        loop(
            header = {
                conditionalBranch(
                    condition = isNull(currentWeakRefCollPtrPtrPtr.dereference().dereference()),
                    ifTrue = {
                        breakLoop()
                    }
                )
                doIteration()
            },
            body = collIterBody@{
                store(context.word(0), to = currentCollIndexPtr)
                loop(
                    header = innerHeader@{
                        conditionalBranch(
                            condition = icmp(currentCollIndexPtr.dereference(), LlvmIntPredicate.EQUAL, context.word(EmergeWeakReferenceCollectionType.pointersToWeakReferences.type.elementCount)),
                            ifTrue = {
                                this@innerHeader.breakLoop()
                            }
                        )
                        this@innerHeader.doIteration()
                    },
                    body = collEntryIterBody@{
                        val currentColIndexValue = currentCollIndexPtr.dereference()
                        val entryPtr = getelementptr(currentWeakRefCollPtrPtrPtr.dereference().dereference())
                            .member { pointersToWeakReferences }
                            .index(currentColIndexValue)
                            .get()
                        val entryValue = entryPtr.dereference()
                        conditionalBranch(
                            condition = isEq(entryValue, pointerToWeakReference),
                            ifTrue = {
                                store(context.nullValue(pointerTo(PointerToAnyEmergeValue)), to = entryPtr)
                                retVoid()
                            }
                        )
                        store(
                            add(currentColIndexValue, context.word(1)),
                            to = currentCollIndexPtr
                        )
                        this@collEntryIterBody.loopContinue()
                    }
                )
                // the current collection doesn't have any free slots, try the next
                val nextCollPtrPtr = getelementptr(currentWeakRefCollPtrPtrPtr.dereference().dereference())
                    .member { next }
                    .get()
                store(nextCollPtrPtr, to = currentWeakRefCollPtrPtrPtr)
                this@collIterBody.loopContinue()
            }
        )
        inlinePanic("weak reference is not registered, cannot unregister")
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
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.AlwaysInline)
    functionAttribute(LlvmFunctionAttribute.NoFree)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)

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
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.WillReturn)
    functionAttribute(LlvmFunctionAttribute.AlwaysInline)
    functionAttribute(LlvmFunctionAttribute.NoFree)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)

    val inputRef by param(PointerToAnyEmergeValue)

    body {
        conditionalBranch(isNotNull(inputRef), ifTrue = {
            callIntrinsic(afterReferenceCreatedNonNullable, listOf(inputRef))
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
        callIntrinsic(afterReferenceCreatedNullable, listOf(this))
    } else {
        callIntrinsic(afterReferenceCreatedNonNullable, listOf(this))
    }
}

/**
 * A no-op iff the [emergeType] is a value-type.
 *
 * Otherwise, increments the reference counter, potentially guarded by a null-check if [IrType.isNullable]
 * is `true`.
 */
context(BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun LlvmValue<LlvmType>.afterReferenceCreated(
    emergeType: IrType,
) {
    if (emergeType.autoboxer != null || type == LlvmVoidType) {
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
        val referenceCountPtr = getelementptr(objectPtr).member { strongReferenceCount }.get()
        val decremented = sub(referenceCountPtr.dereference(), context.word(1))
        val isZero = icmp(decremented, LlvmIntPredicate.EQUAL, context.word(0))
        conditionalBranch(isZero, ifTrue = {
            callIntrinsic(nullWeakReferences, listOf(objectPtr))
            val typeinfoPtr = getelementptr(objectPtr)
                .member { typeinfo }
                .get()
                .dereference()
            val finalizerFn = getelementptr(typeinfoPtr)
                .member { anyValueVirtuals }
                .member { finalizeFunction }
                .get()
                .dereference()

            call(finalizerFn, EmergeAnyValueVirtualsType.finalizeFunctionType, listOf(objectPtr))

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
        conditionalBranch(condition = isNotNull(this), ifTrue = {
            callIntrinsic(dropReferenceFunction, listOf(this@afterReferenceDropped))
            concludeBranch()
        })
    } else {
        callIntrinsic(dropReferenceFunction, listOf(this@afterReferenceDropped))
    }
}

/**
 * A no-op iff the [emergeType] is a value-type.
 *
 * Otherwise, emits a call to [dropReferenceFunction], potentially guarded by a null-check if [IrType.isNullable]
 * is `true`.
 */
context(BasicBlockBuilder<EmergeLlvmContext, *>)
internal fun LlvmValue<LlvmType>.afterReferenceDropped(
    emergeType: IrType,
) {
    if (emergeType.autoboxer != null || type == LlvmVoidType) {
        return
    }

    this.reinterpretAs(PointerToAnyEmergeValue).afterReferenceDropped(emergeType.isNullable)
}

/**
 * for print-debugging intrinsics, is not supposed to be used in productive code
 */
private fun BasicBlockBuilder<*, *>.debugPrint(msg: String) {
    val writeFnValue = Llvm.LLVMGetNamedFunction(context.module, "write") ?: throw CodeGenerationException("Function write not defined in module")
    val writeFn = LlvmFunction(LlvmConstant(writeFnValue, LlvmFunctionAddressType), LlvmFunctionType(LlvmVoidType, listOf(
        LlvmI32Type,
        LlvmPointerType(LlvmI8Type),
        EmergeWordType,
    )))
    val msgBytes = (msg + "\n").toByteArray()
    val dataConstant = LlvmArrayType(msgBytes.size.toLong(), LlvmI8Type).buildConstantIn(context, msgBytes.map { context.i8(it) })
    val dataGlobal = context.addGlobal(dataConstant, LlvmThreadLocalMode.LOCAL_EXEC)
    call(writeFn, listOf(
        context.i32(1),
        getelementptr(dataGlobal)
            .index(context.word(0))
            .get(),
        context.word(msgBytes.size),
    ))
}

/**
 * for print-debugging intrinsics, is not supposed to be used in productive code
 */
private fun BasicBlockBuilder<*, *>.debugIsNull(prefix: String, ptr: LlvmValue<LlvmPointerType<*>>) {
    conditionalBranch(
        condition = isNull(ptr),
        ifTrue = { debugPrint("$prefix is null"); concludeBranch() },
        ifFalse = { debugPrint("$prefix is not null"); concludeBranch() }
    )
}