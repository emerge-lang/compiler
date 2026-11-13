package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction.Companion.callIntrinsic
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.i1
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmIntPredicate
import io.github.tmarsteel.emerge.backend.llvm.llvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.rootSignatureHash

internal val lazyGetFunction = KotlinLlvmFunction.define<EmergeLlvmContext, _>(
    "emerge.core.Lazy::value",
    PointerToAnyEmergeValue,
) {
    val self by param(PointerToAnyEmergeValue)

    body {
        val selfAsLazy = self.reinterpretAs(pointerTo(context.lazyType))

        val isInitializedPtr = getelementptr(selfAsLazy)
            .member(context.lazyType.irClass.fieldOfMemberVariable("initialized"))
            .get()
            .reinterpretAs(pointerTo(LlvmBooleanType))

        val valueFieldPtr = getelementptr(selfAsLazy)
            .member(context.lazyType.irClass.fieldOfMemberVariable("_value"))
            .get()
            .reinterpretAs(pointerTo(PointerToAnyEmergeValue))

        conditionalBranch(
            condition = icmp(isInitializedPtr.dereference(), LlvmIntPredicate.EQUAL, context.i1(false)),
            ifTrue = {
                val initializerPtr = getelementptr(selfAsLazy)
                    .member(context.lazyType.irClass.fieldOfMemberVariable("initializer"))
                    .get()
                    .dereference()

                val irInitFn = context.lazyInitializerType.irClass.memberFunctions.flatMap { it.overloads }.single()
                assert(irInitFn.canonicalName.simpleName == "computeValue")
                assert(irInitFn.parameters.size == 1)
                assert(irInitFn.typeParameters.size == 1)

                val initFn = callIntrinsic(getDynamicCallAddress, listOf(
                    initializerPtr,
                    context.uWord(irInitFn.rootSignatureHash),
                ))
                val value = call(initFn, irInitFn.llvmFunctionType, listOf(initializerPtr))
                    .reinterpretAs(PointerToAnyEmergeValue)
                store(value, valueFieldPtr)
                // the refcount +1 for returning the value from the initializer to this code matches the needed +1 for storing it

                concludeBranch()
            }
        )

        val value = valueFieldPtr.dereference()
        value.afterReferenceCreated(true)
        ret(value)
    }
}