package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode

val panic = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>("emerge.platform.panic", LlvmVoidType) {
    functionAttribute(LlvmFunctionAttribute.NoFree)
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.NoReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)

    val message by param(PointerToAnyEmergeValue)

    body {
        val panicPrefixData = "PANIC! ".toByteArray(Charsets.UTF_8).map { context.i8(it) }
        val panicPrefixGlobal = context.addGlobal(LlvmArrayType(panicPrefixData.size.toLong(), LlvmI8Type).buildConstantIn(context, panicPrefixData), LlvmThreadLocalMode.NOT_THREAD_LOCAL)

        val writeFnAddr = context.getNamedFunctionAddress("write")!!
        // fd: S32, buf: COpaquePointer, count: UWord) -> SWord
        val writeFnType = LlvmFunctionType(EmergeWordType, listOf(LlvmI32Type, pointerTo(LlvmI8Type), EmergeWordType))

        call(writeFnAddr, writeFnType, listOf(
            context.i32(2), // STDERR
            panicPrefixGlobal,
            context.word(panicPrefixGlobal.type.pointed.elementCount),
        ))
        val pointerToMessageDataArray = getelementptr(message.reinterpretAs(pointerTo(context.stringType)))
            .member(context.stringType.irClass.memberVariables.single { it.name == "utf8Data" })
            .get()
            .dereference()
            .reinterpretAs(pointerTo(EmergeS8ArrayType))
        val messageLength = getelementptr(pointerToMessageDataArray)
            .member { base }
            .member { elementCount }
            .get()
            .dereference()
        val pointerToMessageData = getelementptr(pointerToMessageDataArray)
            .member { elements }
            .get()
        call(writeFnAddr, writeFnType, listOf(
            context.i32(2),
            pointerToMessageData,
            messageLength,
        ))

        val exitFnAddr = context.getNamedFunctionAddress("exit")!!
        val exitFnType = LlvmFunctionType(LlvmVoidType, emptyList())
        call(exitFnAddr, exitFnType, emptyList())
        retVoid()
    }
}