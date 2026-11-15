package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction.Companion.callIntrinsic
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.i1
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.abortOnException
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.fallibleSuccess
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
import io.github.tmarsteel.emerge.backend.llvm.llvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.signatureHashes

internal val lazyGetFunction: KotlinLlvmFunction<EmergeLlvmContext, EmergeFallibleCallResult.WithValue<LlvmPointerType<out EmergeHeapAllocated>>> = KotlinLlvmFunction.define(
    "emerge.core.Lazy::value",
    EmergeFallibleCallResult.ofEmergeReference,
) {
    val self by param(PointerToAnyEmergeValue)

    body {
        val lazyClass = context.lazyType.irClass
        val selfAsLazy = self.reinterpretAs(pointerTo(context.lazyType))

        val initializedPtr = getelementptr(selfAsLazy)
            .member(lazyClass.fieldOfMemberVariable("initialized"))
            .get()
            .reinterpretAs(pointerTo(LlvmBooleanType))

        val initializingPtr = getelementptr(selfAsLazy)
            .member(lazyClass.fieldOfMemberVariable("initializing"))
            .get()
            .reinterpretAs(pointerTo(LlvmBooleanType))

        val valueField = lazyClass.fieldOfMemberVariable("_value")
        val valueFieldPtr = getelementptr(selfAsLazy)
            .member(valueField)
            .get()
            .reinterpretAs(pointerTo(PointerToAnyEmergeValue))

        conditionalBranch(
            condition = icmp(initializedPtr.dereference(), LlvmIntPredicate.EQUAL, context.i1(false)),
            ifTrue = {
                conditionalBranch(
                    condition = initializingPtr.dereference(),
                    ifTrue = {
                        inlinePanic("the initializer of a ${lazyClass.canonicalName.simpleName} accessed its value")
                    },
                )
                store(context.i1(true), initializingPtr)

                val initializer = getelementptr(selfAsLazy)
                    .member(lazyClass.fieldOfMemberVariable("initializer"))
                    .get()
                    .reinterpretAs(pointerTo(PointerToAnyEmergeValue))
                    .dereference()

                val computeValueFn = context.lazyInitializerInterface.memberFunctions
                    .flatMap { it.overloads }
                    .single { it.canonicalName.simpleName == "computeValue" && it.parameters.size == 1 }
                val computeValueAddress = callIntrinsic(getDynamicCallAddress, listOf(
                    initializer,
                    context.uWord(computeValueFn.signatureHashes.first()),
                ))
                @Suppress("UNCHECKED_CAST")
                val value = call(
                    computeValueAddress,
                    computeValueFn.llvmFunctionType as LlvmFunctionType<EmergeFallibleCallResult<LlvmPointerType<out EmergeHeapAllocated>>>,
                    listOf(initializer),
                ).abortOnException { exceptionPtr ->
                    // the next access tries again
                    store(context.i1(false), initializingPtr)
                    propagateOrPanic(exceptionPtr)
                }

                // the reference returned by the initializer is the one held by the field
                store(value, valueFieldPtr)
                store(context.i1(true), initializedPtr)
                store(context.i1(false), initializingPtr)

                concludeBranch()
            }
        )

        val value = valueFieldPtr.dereference()
        value.afterReferenceCreated(isNullable = true)
        ret(fallibleSuccess(value))
    }
}
