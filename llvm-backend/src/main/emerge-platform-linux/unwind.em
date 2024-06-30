package emerge.platform

import emerge.ffi.c.COpaquePointer
import emerge.ffi.c.CPointer
import emerge.std.collections.ArrayList
import emerge.core.StackTraceElement
import emerge.core.FilledStackTraceElement
import emerge.core.ErrorStackTraceElement
import emerge.linux.libc.exit

// translated from gccs libbacktrace headers (libbacktrace/backtrace.h)

// TODO: the callback parameters must be declared external(C)
// however, this (correctly) forces them to be nothrow, too. This is impossible right now
// because the callbacks need to allocate heap memory, which can throw an OOM error
// also, the necessary try-catch to handle that OOM is not implemented in the compiler, yet

private external(C) nothrow read fn backtrace_create_state<Data : CPointer<out Any?>?>(
    filename: Nothing?,
    threaded: S32,
    borrow error_callback: mut (Data, COpaquePointer, S32) -> Unit,
    data: Data,
) -> COpaquePointer

private external(C) nothrow read fn backtrace_simple<Data : CPointer<out Any?>?>(
    state: COpaquePointer,
    skip: U32,
    borrow callback: read (Data, UWord) -> S32,
    borrow errorCallback: mut (Data, COpaquePointer, S32) -> Unit,
    data: Data,
) -> S32

private external(C) nothrow fn backtrace_pcinfo<Data : CPointer<out Any?>?>(
    state: COpaquePointer,
    pc: UWord,
    borrow fullCallback: (Data, UWord, COpaquePointer, S32, COpaquePointer) -> S32,
    borrow errorCallback: (Data, COpaquePointer, S32) -> Unit,
    data: Data,
) -> S32

private mut fn backtraceCallback_stateCreateError(data: CPointer<Nothing>?, errorMessageStr: COpaquePointer, errorCode: S32) -> Unit {
    printError("backtrace_create_state errored: code " + errorCode.toString())
    exit(-1)
}

private var backtraceState: COpaquePointer = backtrace_create_state::<CPointer<Nothing>?>(null, 0, ::backtraceCallback_stateCreateError, null)

private class PreliminaryStackTraceElement {
    instructionPointer: UWord = init
    var procedureName: const String? = null
    var fileName: const String? = null
    var lineNumber: U32 = 0
}

private read fn backtraceCallback_simple_regular(data: CPointer<mut ArrayList<const StackTraceElement>>, instructionPointer: UWord) -> S32 {
    pste: exclusive _ = PreliminaryStackTraceElement(instructionPointer)
    ste = FilledStackTraceElement(pste.instructionPointer, pste.procedureName, pste.fileName, pste.lineNumber)
    data.pointed.add(ste)
    return 0
}

private fn backtraceCallback_simple_error(data: CPointer<mut ArrayList<const StackTraceElement>>, errorMessage: COpaquePointer, errorCode: S32) -> Unit {
    data.pointed.add(ErrorStackTraceElement("backtrace_simple error with code " + errorCode.toString()))
}

export read fn collectStackTrace() -> read ArrayList<const StackTraceElement> {
    var list = ArrayList::<const StackTraceElement>()
    backtrace_simple::<CPointer<mut ArrayList<const StackTraceElement>>>(
        backtraceState,
        0,
        ::backtraceCallback_simple_regular,
        ::backtraceCallback_simple_error,
        CPointer(list)
    )

    return list
}