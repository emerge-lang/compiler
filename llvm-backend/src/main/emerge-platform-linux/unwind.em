package emerge.platform

import emerge.ffi.c.COpaquePointer
import emerge.ffi.c.CPointer
import emerge.std.collections.ArrayList
import emerge.core.StackTraceElement

// translated from gccs libbacktrace headers (libbacktrace/backtrace.h)

private external(C) nothrow read fn backtrace_create_state<Data>(
    filename: Nothing?,
    threaded: S32,
    borrow error_callback: (CPointer<Data>, COpaquePointer, S32) -> Unit,
    data: CPointer<Data>,
) -> COpaquePointer

private external(C) nothrow read fn backtrace_simple<Data>(
    state: COpaquePointer,
    skip: U32,
    borrow callback: (CPointer<Data>, UWord) -> S32,
    borrow errorCallback: (CPointer<Data>, COpaquePointer, S32) -> Unit,
    data: CPointer<Data>,
) -> S32

private external(C) nothrow fn backtrace_pcinfo<Data>(
    state: COpaquePointer,
    pc: UWord,
    borrow fullCallback: (CPointer<Data>, UWord, COpaquePointer, S32, COpaquePointer) -> S32,
    borrow errorCallback: (CPointer<Data>, COpaquePointer, S32) -> Unit,
    data: CPointer<Data>,
) -> S32

export read fn collectStackTrace() -> ArrayList<StackTraceElement> {
    panic("not implemented")
    return null!!
}