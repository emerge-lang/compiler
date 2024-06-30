package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI32Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmI8Type
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmPointerType.Companion.pointerTo
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmValue
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmVoidType
import io.github.tmarsteel.emerge.backend.llvm.dsl.buildConstantIn
import io.github.tmarsteel.emerge.backend.llvm.dsl.i32
import io.github.tmarsteel.emerge.backend.llvm.dsl.i8
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeClassType.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode

private fun BasicBlockBuilder<*, *>.buildStdErrPrinter(): (LlvmValue<LlvmPointerType<*>>, LlvmValue<EmergeWordType>) -> Unit {
    val writeFnAddr = context.getNamedFunctionAddress("write")!!
    // fd: S32, buf: COpaquePointer, count: UWord) -> SWord
    val writeFnType = LlvmFunctionType(EmergeWordType, listOf(LlvmI32Type, pointerTo(LlvmVoidType), EmergeWordType))

    return { dataPtr: LlvmValue<LlvmPointerType<*>>, dataLen: LlvmValue<EmergeWordType> ->
        call(writeFnAddr, writeFnType, listOf(
            context.i32(2), // FD_STDERR
            dataPtr,
            dataLen
        ))
    }
}

private fun BasicBlockBuilder<*, *>.printLinefeed(printer: (LlvmValue<LlvmPointerType<*>>, LlvmValue<EmergeWordType>) -> Unit) {
    val linefeedData = alloca(LlvmI8Type)
    store(context.i8(10), linefeedData)
    printer(linefeedData, context.word(1))
}

private fun BasicBlockBuilder<*, *>.printStackTraceToStdErr() {
    val fnName = "emerge.platform.printStackTraceToStandardError"
    val printStackFnAddr = context.getNamedFunctionAddress(fnName) ?: throw CodeGenerationException("Could not find $fnName")
    val printStackFnType = LlvmFunctionType(LlvmBooleanType, emptyList())
    call(printStackFnAddr, printStackFnType, emptyList())
}

private fun BasicBlockBuilder<*, *>.exit(): BasicBlockBuilder.Termination {
    val exitFnAddr = context.getNamedFunctionAddress("exit")!!
    val exitFnType = LlvmFunctionType(LlvmVoidType, emptyList())
    call(exitFnAddr, exitFnType, emptyList())
    return unreachable()
}

val panic = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>("emerge.platform.panic", LlvmVoidType) {
    functionAttribute(LlvmFunctionAttribute.NoFree)
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.NoReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)

    val message by param(PointerToAnyEmergeValue)

    body {
        val panicPrefixData = "PANIC! ".toByteArray(Charsets.UTF_8).map { context.i8(it) }
        val panicPrefixGlobal = context.addGlobal(LlvmArrayType(panicPrefixData.size.toLong(), LlvmI8Type).buildConstantIn(context, panicPrefixData), LlvmThreadLocalMode.NOT_THREAD_LOCAL)

        val writeToStdErr = buildStdErrPrinter()
        writeToStdErr(panicPrefixGlobal, context.word(panicPrefixGlobal.type.pointed.elementCount))
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
        writeToStdErr(pointerToMessageData, messageLength)
        printLinefeed(writeToStdErr)
        printStackTraceToStdErr()

        exit()
    }
}

fun BasicBlockBuilder<out LlvmContext, *>.inlinePanic(message: String): BasicBlockBuilder.Termination {
    val panicMessageData = "PANIC! $message".toByteArray(Charsets.UTF_8).map { context.i8(it) }
    val panicMessageGlobal = context.addGlobal(LlvmArrayType(panicMessageData.size.toLong(), LlvmI8Type).buildConstantIn(context, panicMessageData), LlvmThreadLocalMode.NOT_THREAD_LOCAL)

    val writeToStdErr = buildStdErrPrinter()
    writeToStdErr(panicMessageGlobal, context.word(panicMessageGlobal.type.pointed.elementCount))
    printLinefeed(writeToStdErr)
    printStackTraceToStdErr()

    return exit()
}