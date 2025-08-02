package io.github.tmarsteel.emerge.backend.llvm.intrinsics

import io.github.tmarsteel.emerge.backend.api.ir.IrClass
import io.github.tmarsteel.emerge.backend.llvm.codegen.anyValueBase
import io.github.tmarsteel.emerge.backend.llvm.codegen.emitRead
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
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.abortOnException
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.fallibleFailure
import io.github.tmarsteel.emerge.backend.llvm.intrinsics.EmergeFallibleCallResult.Companion.handle
import io.github.tmarsteel.emerge.backend.llvm.jna.LlvmThreadLocalMode
import io.github.tmarsteel.emerge.backend.llvm.linux.libcWriteFunction
import io.github.tmarsteel.emerge.backend.llvm.llvmRef
import io.github.tmarsteel.emerge.backend.llvm.signatureHashes

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

private fun BasicBlockBuilder<*, *>.printConstantString(printer: (LlvmValue<LlvmPointerType<*>>, LlvmValue<EmergeWordType>) -> Unit, str: String) {
    val constant = context.constantString(str)
    printer(constant, context.word(constant.type.pointed.elementCount))
}

context(builder: BasicBlockBuilder<*, *>)
private val LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>.typeName: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>> get() {
    with(builder) {
        return this@typeName.anyValueBase()
            .member { typeinfo }
            .let { getelementptr(it.get().dereference()) }
            .member { canonicalNamePtr }
            .get()
            .dereference()
    }
}

private fun BasicBlockBuilder<out EmergeLlvmContext, *>.printStackTraceToStdErr() {
    call(context.printStackTraceToStdErrFunction, emptyList())
}

private fun BasicBlockBuilder<EmergeLlvmContext, *>.printEmergeString(
    printer: (LlvmValue<LlvmPointerType<*>>, LlvmValue<EmergeWordType>) -> Unit,
    stringPtr: LlvmValue<LlvmPointerType<out EmergeHeapAllocated>>,
) {
    val utf8DataField = context.stringType.irClass.memberVariables
        .single { it.name == "utf8Data" }
        .let { it.readStrategy as IrClass.MemberVariable.AccessStrategy.BareField }
        .let { readStrat -> context.stringType.irClass.fields.single { it.id == readStrat.fieldId } }

    val pointerToMessageDataArray = getelementptr(stringPtr.reinterpretAs(pointerTo(context.stringType)))
        .member(utf8DataField)
        .get()
        .dereference()
        .reinterpretAs(pointerTo(EmergeS8ArrayType))
    val messageLength = getelementptr(pointerToMessageDataArray)
        .member { base }
        .member { EmergeArrayBaseType.elementCount }
        .get()
        .dereference()
    val pointerToMessageData = getelementptr(pointerToMessageDataArray)
        .member { elements }
        .get()

    printer(pointerToMessageData, messageLength)
}

private fun BasicBlockBuilder<*, *>.exit(status: UByte): BasicBlockBuilder.Termination {
    val exitFnAddr = context.getNamedFunctionAddress("exit")!!
    val exitFnType = LlvmFunctionType(LlvmVoidType, listOf(LlvmI32Type))
    call(exitFnAddr, exitFnType, listOf(context.i32(status.toUInt())))
    return unreachable()
}

val panicOnString = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>("emerge.platform.panic", LlvmVoidType) {
    functionAttribute(LlvmFunctionAttribute.NoFree)
    functionAttribute(LlvmFunctionAttribute.NoUnwind)
    functionAttribute(LlvmFunctionAttribute.NoReturn)
    functionAttribute(LlvmFunctionAttribute.NoRecurse)

    val message by param(PointerToAnyEmergeValue)

    body {
        val writeToStdErr = buildStdErrPrinter()
        printConstantString(writeToStdErr, "PANIC! ")
        printEmergeString(writeToStdErr, message)
        printLinefeed(writeToStdErr)
        printStackTraceToStdErr()

        exit(1u)
    }
}

fun BasicBlockBuilder<out EmergeLlvmContext, *>.inlinePanic(message: String): BasicBlockBuilder.Termination {
    val writeToStdErr = buildStdErrPrinter()
    printConstantString(writeToStdErr, "PANIC! $message")
    printLinefeed(writeToStdErr)
    printStackTraceToStdErr()

    return exit(1u)
}

internal fun BasicBlockBuilder<out EmergeLlvmContext, out EmergeFallibleCallResult<*>>.inlineThrow(
    exceptionClass: IrClass,
    ctorArguments: List<LlvmValue<*>>,
): BasicBlockBuilder.Termination {
    val exceptionPtr = call(exceptionClass.constructor.llvmRef!!, ctorArguments)
        .reinterpretAs(EmergeFallibleCallResult.ofEmergeReference)
        .abortOnException { exceptionCtorException ->
            propagateOrPanic(exceptionCtorException)
        }

    val fillStackTraceIrFn = context.throwableClazz.memberFunctions
        .single { it.canonicalName.simpleName == "fillStackTrace" }
        .overloads
        .single()

    val fillStackTraceFnAddress = call(context.registerIntrinsic(getDynamicCallAddress), listOf(
        exceptionPtr,
        context.word(fillStackTraceIrFn.signatureHashes.first()),
    ))

    call(
        fillStackTraceFnAddress,
        LlvmFunctionType(EmergeFallibleCallResult.OfVoid, listOf(PointerToAnyEmergeValue)),
        listOf(exceptionPtr),
    )
        .abortOnException { _ ->
            // ignore this one
            propagateOrPanic(exceptionPtr)
        }

    return fallibleFailure(exceptionPtr)
}

private val displayThrowableToStdErr = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>(
    "emerge.core.displayThrowableToStandardError",
    LlvmVoidType
) {
    val exceptionPtr by param(PointerToAnyEmergeValue)

    body {
        val writeToStdErr = buildStdErrPrinter()
        val printToResult = call(
            context.printThrowableFunction,
            listOf(exceptionPtr, context.standardErrorStreamGlobalVar.declaration.emitRead!!(this)),
        )

        if (printToResult.type is EmergeFallibleCallResult<*>) {
            (printToResult as LlvmValue<EmergeFallibleCallResult.OfVoid>).handle(
                regularBranch = { concludeBranch() },
                exceptionBranch = { printToException ->
                    printConstantString(writeToStdErr, "Caught exception while printing the stacktrace of ")
                    printEmergeString(writeToStdErr, exceptionPtr.typeName)
                    printLinefeed(writeToStdErr)
                    printConstantString(writeToStdErr, "This exception was caught while printing the stack trace: ")
                    printEmergeString(writeToStdErr, printToException.typeName)
                    printLinefeed(writeToStdErr)
                    concludeBranch()
                }
            )
        } else {
            // nothrow, yey, nothing to do!
        }

        retVoid()
    }
}

internal val panicOnThrowable = KotlinLlvmFunction.define<EmergeLlvmContext, LlvmVoidType>("emerge.platform.panicOnThrowable", LlvmVoidType) {
    val exceptionPtr by param(PointerToAnyEmergeValue)

    functionAttribute(LlvmFunctionAttribute.NoRecurse)
    functionAttribute(LlvmFunctionAttribute.NoReturn)

    body {
        val writeToStdErr = buildStdErrPrinter()

        printConstantString(writeToStdErr, "PANIC! unhandled exception\n")
        call(context.registerIntrinsic(displayThrowableToStdErr), listOf(exceptionPtr))
        printConstantString(writeToStdErr, "\nthis panic was triggered from this call chain:\n")
        printStackTraceToStdErr()
        exit(1u)
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