package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder
import io.github.tmarsteel.emerge.backend.llvm.dsl.BasicBlockBuilder.Companion.retVoid
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.index
import io.github.tmarsteel.emerge.backend.llvm.dsl.GetElementPointerStep.Companion.member
import io.github.tmarsteel.emerge.backend.llvm.dsl.KotlinLlvmFunction
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmArrayType
import io.github.tmarsteel.emerge.backend.llvm.dsl.LlvmBooleanType
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

// TODO: rename file to panic.kt

private fun BasicBlockBuilder<*, *>.buildPrinter(fd: LlvmValue<LlvmI32Type>): (LlvmValue<LlvmPointerType<*>>, LlvmValue<EmergeWordType>) -> Unit {
    val writeFnAddr = context.getNamedFunctionAddress("write")!!
    // fd: S32, buf: COpaquePointer, count: UWord) -> SWord
    val writeFnType = LlvmFunctionType(EmergeWordType, listOf(LlvmI32Type, pointerTo(LlvmVoidType), EmergeWordType))

    return { dataPtr: LlvmValue<LlvmPointerType<*>>, dataLen: LlvmValue<EmergeWordType> ->
        call(writeFnAddr, writeFnType, listOf(
            fd,
            dataPtr,
            dataLen
        ))
    }
}

private fun BasicBlockBuilder<*, *>.buildStdErrPrinter(): (LlvmValue<LlvmPointerType<*>>, LlvmValue<EmergeWordType>) -> Unit {
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

private fun BasicBlockBuilder<*, *>.printStackTraceToStdErr() {
    val fnName = "emerge.platform.printStackTraceToStandardError"
    val printStackFnAddr = context.getNamedFunctionAddress(fnName) ?: throw CodeGenerationException("Could not find $fnName")
    val printStackFnType = LlvmFunctionType(LlvmBooleanType, emptyList())
    call(printStackFnAddr, printStackFnType, emptyList())
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

fun BasicBlockBuilder<out LlvmContext, *>.inlinePanic(message: String): BasicBlockBuilder.Termination {
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
        inlinePanic("unhandled exception")
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