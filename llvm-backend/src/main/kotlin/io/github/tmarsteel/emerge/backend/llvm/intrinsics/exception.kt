package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmContext
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionAttribute
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmFunctionType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmGlobal
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
import io.github.tmarsteel.emerge.backend.llvm.linux.libcWriteFunction

// TODO: rename file to panic.kt

private fun BasicBlockBuilder<out EmergeLlvmContext, *>.buildPrinter(fd: LlvmValue<LlvmI32Type>): (LlvmValue<LlvmPointerType<*>>, LlvmValue<EmergeWordType>) -> Unit {
    return { dataPtr: LlvmValue<LlvmPointerType<*>>, dataLen: LlvmValue<EmergeWordType> ->
        call(context.libcWriteFunction, listOf(
            fd,
            dataPtr,
            dataLen
        ))
    }
}

private fun BasicBlockBuilder<out EmergeLlvmContext, *>.buildStdErrPrinter(): (LlvmValue<LlvmPointerType<*>>, LlvmValue<EmergeWordType>) -> Unit {
    return buildPrinter(context.i32(2) /* FD_STDERR */)
}

private fun LlvmContext.constantString(data: String): LlvmGlobal<LlvmArrayType<LlvmI8Type>> {
    val bytes = data.toByteArray(Charsets.UTF_8).map { i8(it) }
    return addGlobal(
        LlvmArrayType(bytes.size.toLong(), LlvmI8Type).buildConstantIn(this, bytes),
        LlvmThreadLocalMode.NOT_THREAD_LOCAL
    )
}

private fun BasicBlockBuilder<*, *>.printLinefeed(printer: (LlvmValue<LlvmPointerType<*>>, LlvmValue<EmergeWordType>) -> Unit) {
    val linefeedData = alloca(LlvmI8Type)
    store(context.i8(10), linefeedData)
    printer(linefeedData, context.word(1))
}

private fun BasicBlockBuilder<out EmergeLlvmContext, *>.printStackTraceToStdErr() {
    call(context.printStackTraceToStdErrFunction, emptyList())
}

private fun BasicBlockBuilder<*, *>.exit(status: UByte): BasicBlockBuilder.Termination {
    val exitFnAddr = context.getNamedFunctionAddress("exit")!!
    val exitFnType = LlvmFunctionType(LlvmVoidType, listOf(LlvmI32Type))
    call(exitFnAddr, exitFnType, listOf(context.i32(status.toUInt())))
    return unreachable()
}

val panic = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>("emerge.platform.panic", LlvmVoidType) {
    functionAttribute(LlvmFunctionAttribute.NoFree)
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.NoReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)

    val message by param(PointerToAnyEmergeValue)

    body {
        val panicPrefixGlobal = context.constantString("PANIC! ")

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

        exit(1u)
    }
}

fun BasicBlockBuilder<out EmergeLlvmContext, *>.inlinePanic(message: String): BasicBlockBuilder.Termination {
    val panicMessageGlobal = context.constantString("PANIC! $message")

    val writeToStdErr = buildStdErrPrinter()
    writeToStdErr(panicMessageGlobal, context.word(panicMessageGlobal.type.pointed.elementCount))
    printLinefeed(writeToStdErr)
    printStackTraceToStdErr()

    return exit(1u)
}

internal val panicOnThrowable = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>("emerge.platform.panicOnThrowable", LlvmVoidType) {
    val exceptionPtr by param(PointerToAnyEmergeValue)

    functionAttribute(LlvmFunctionAttribute.NoRecurse)
    functionAttribute(LlvmFunctionAttribute.NoReturn)

    body {
        call(context.panicOnThrowableFunction, listOf(exceptionPtr))
        unreachable()
    }
}

internal val writeMemoryAddress = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>("emerge.platform.writeMemoryAddress", LlvmVoidType) {
    val address by param(EmergeWordType)
    val fd by param(LlvmI32Type)

    body {
        val prefixGlobal = context.constantString("0x")

        val writer = buildPrinter(fd)
        writer(prefixGlobal, context.word(prefixGlobal.type.pointed.elementCount))

        val nibbleCharsGlobal = context.constantString("0123456789abcdef")

        IntProgression.fromClosedRange(
            rangeStart = EmergeWordType.getNBitsInContext(context) - 4,
            rangeEnd = 0,
            step = -4
        ).forEach { shrAmount ->
            val nibble = and(lshr(address, context.word(shrAmount)), context.word(0b1111))
            writer(
                getelementptr(nibbleCharsGlobal).index(nibble).get(),
                context.word(1),
            )
        }

        retVoid()
    }
}