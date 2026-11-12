package emerge.platform

import emerge.core.unwind.StackTraceElement
import emerge.std.collections.ArrayList
import emerge.core.range.Iterable
import emerge.ffi.c.addressOfFirst
import emerge.ffi.c.COpaquePointer
import emerge.linux.libc.write

read fn collectStackTrace(borrow collector: mut StackTraceCollector, nFramesToSkip: U32, includeRuntimeFrames: Bool) -> own Iterable<const StackTraceElement> {
    // the logic around the context and cursor buffers cannot be moved into emerge classes
    // the reason is that it matters very much on which stack frame unw_create_context and unw_init_local
    // are being called. They need to be called from the same stack frame. Additionally, when a function
    // returns, any unwind cursor has to have been unwound past that stackframe, otherwise unwinding will be UB

    stackList: own _ = ArrayList::<const StackTraceElement>()
    var contextBuffer = Array.new::<S8>(unwind_context_size(), 0 as S8)
    var errorCode = unw_getcontext(contextBuffer.addressOfFirst())
    if errorCode != UNWIND_ERROR_SUCCESS {
        panic("unw_getcontext errored: " + unwindErrorToString(errorCode))
    }

    var cursorBuffer = Array.new::<S8>(unwind_cursor_size(), 0 as S8)
    set errorCode = unw_init_local(cursorBuffer.addressOfFirst(), contextBuffer.addressOfFirst())
    if errorCode != UNWIND_ERROR_SUCCESS {
        panic("unw_init_local errored: " + unwindErrorToString(errorCode))
    }

    var nSkipped = 0 as U32
    do {
        procName = unwindCursorGetProcedureName(cursorBuffer.addressOfFirst())
        if (not includeRuntimeFrames) and procName == "main" {
            break
        }
    
        if nSkipped >= nFramesToSkip {
            ip = unwindCursorGetInstructionPointer(cursorBuffer.addressOfFirst(), collector.registerBuffer)

            stackList.add(StackTraceElement(ip, procName))
        } else {
            set nSkipped = nSkipped + 1
        }
    } while (unwindCursorTryStepUp(cursorBuffer.addressOfFirst()))

    return stackList
}

// these structures are from LLVM-20s libunwind (libunwindh.h)
// this works because right now, emerge classes have a layout identical to that of C structs
// by the virtue of using LLVM and not re-ordering class variables to save space
// this should be denoted ASAP with an attribute like rusts #[repr(C)] or another mechanism
// of telling the compiler about the desired layout of a type

// the nongnu libunwind has a good documentation of the API: https://www.nongnu.org/libunwind/docs.html

UNWIND_ERROR_SUCCESS: S32                     =  0
UNWIND_ERROR_UNSPECIFIED: S32                 = -1
UNWIND_ERROR_OOM: S32                         = -2
UNWIND_ERROR_BAD_REGISTER: S32                = -3
UNWIND_ERROR_READONLY_REGISTER: S32           = -4  // attempt to write read-only register
UNWIND_ERROR_STOP: S32                        = -5  // stop unwinding
UNWIND_ERROR_INVALID_INSTRUCTION_POINTER: S32 = -6
UNWIND_ERROR_BAD_FRAME: S32                   = -7
UNWIND_ERROR_INVALID: S32                     = -8  // unsupported operation or bad value
UNWIND_ERROR_UNSUPPORTED_VERSION: S32         = -9
UNWIND_ERROR_NO_INFO: S32                     = -10 // no unwind info found

UNWIND_REGISTER_IP: S32 = 16

private nothrow fn knownUnwindErrorToStringSafe(code: S32) -> String? {
    // TODO: when/switch
    if code == UNWIND_ERROR_SUCCESS {
        return "no error"
    }

    if code == UNWIND_ERROR_UNSPECIFIED {
        return "unspecified error"
    }

    if code == UNWIND_ERROR_OOM {
        return "out of memory"
    }

    if code == UNWIND_ERROR_BAD_REGISTER {
        return "bad register number"
    }

    if code == UNWIND_ERROR_READONLY_REGISTER {
        return "attempt to write read-only register"
    }

    if code == UNWIND_ERROR_STOP {
        return "stop unwinding"
    }

    if code == UNWIND_ERROR_INVALID_INSTRUCTION_POINTER {
        return "invalid instruction pointer"
    }

    if code == UNWIND_ERROR_BAD_FRAME {
        return "bad frame"
    }

    if code == UNWIND_ERROR_INVALID {
        return "unsupported operation or bad value"
    }

    if code == UNWIND_ERROR_UNSUPPORTED_VERSION {
        return "unwind info has unsupported version"
    }

    if code == UNWIND_ERROR_NO_INFO {
        return "no unwind info found"
    }

    return null
}

private nothrow fn unwindErrorToStringSafe(code: S32) -> String {
    return knownUnwindErrorToStringSafe(code)
        ?: "unknown error"
}

private fn unwindErrorToString(code: S32) -> String {
    return knownUnwindErrorToStringSafe(code)
        ?: "unknown error"
        //?: "unknown error (code " + code.toString() + ")"
}

// constants from __libunwind_config.h
// size of unwind contexts
private intrinsic nothrow fn unwind_context_size() -> UWord
// size of unwind cursors
private intrinsic nothrow fn unwind_cursor_size() -> UWord

// initializes the context
// @param context must point to a region of at least [unwind_context_size] size
// @returns an error code
private external(C) read nothrow fn unw_getcontext(context: COpaquePointer) -> S32

// initializes an unwind cursor
// @param cursor the cursor to initialize; must point to a region of at least [unwind_cursor_size] size
// @param context a cursor that was initialized with [unw_getcontext]
// @returns an error code
private external(C) read nothrow fn unw_init_local(cursor: COpaquePointer, context: COpaquePointer) -> S32

// advances the cursor to the previous, less deeply nested stack frame / walks up the stack
// @param cursor a cursor previously initialized with [unw_init_local]
// @return a positive value on success, 0 if there are no more stack frames, or a negative value for an error code
private external(C) read nothrow fn unw_step(cursor: COpaquePointer) -> S32

private external(C) nothrow fn unw_get_reg(cursor: COpaquePointer, register: S32, buf: COpaquePointer) -> S32

private external(C) nothrow fn unw_get_proc_name(cursor: COpaquePointer, buf: COpaquePointer, len: UWord, offp: COpaquePointer) -> S32

private external(C) nothrow fn unw_get_proc_info(cursor: COpaquePointer, buf: COpaquePointer) -> S32

// attempts to move the cursor to the next, less deeply nested tack frame
// @return true if the cursor was successfully moved, false if there are no more stack frames left
// TODO: make pure, change parameter to mut COpaquePointer; needs parameterized mutability for Array.addressOfFirst()
private read fn unwindCursorTryStepUp(cursorPtr: COpaquePointer) -> Bool {
    errorCode = unw_step(cursorPtr)
    if errorCode == UNWIND_ERROR_STOP or errorCode == 0 {
        return false
    }

    if errorCode < 0 {
        panic("unw_step errored: " + unwindErrorToString(errorCode))
    }

    return true
}

private read nothrow fn unwindCursorGetInstructionPointer(cursorPtr: COpaquePointer, borrow registerBuffer: mut Array<UWord>) -> UWord {
    errorCode = unw_get_reg(cursorPtr, UNWIND_REGISTER_IP, registerBuffer.addressOfFirst())
    return registerBuffer.getOrPanic(0)
}

// returns the name of the function belonging to the stack frame this cursor is currently pointing at
private read fn unwindCursorGetProcedureName(cursorPtr: COpaquePointer) -> const String {
    var nameBuf = Array.new::<S8>(256, 0 as S8)
    offpBuf = Array.new::<UWord>(1, 0 as UWord)

    errorCode = unw_get_proc_name(cursorPtr, nameBuf.addressOfFirst(), nameBuf.size, offpBuf.addressOfFirst())
    if errorCode != UNWIND_ERROR_SUCCESS {
        panic("unw_get_proc_name errored: " + unwindErrorToString(errorCode))
    }

    var actualNameLength = 0 as UWord
    while nameBuf[actualNameLength] != 0 and actualNameLength < nameBuf.size {
        set actualNameLength = actualNameLength + 1
    }

    trimmedName: own _ = Array.new::<S8>(actualNameLength, 0 as S8)
    Array.copy(nameBuf, 0, trimmedName, 0, actualNameLength)
    return String(trimmedName)
}

// BEGIN code to print the stack trace during a panic. Is supposed to not do heap
// allocations, avoiding OOM problems during a panic
// this code does, by all my reasoning, not throw. However, the compiler cannot be convinced
// of that right now because some features are lacking. Hence, the functions are not all nothrow
// Collects stack traces. It owns the buffers the unwinder works in; they are allocated when the collector is
// created, so that a stack trace can still be printed when no memory is left.
// The runtime holds one per thread, for `throw` and for panics. Other code obtains one from the root.
export token class StackTraceCollector {
    registerBuffer: mut Array<UWord> = Array.new::<UWord>(1, 0 as UWord)
    backtraceContextBuffer: mut Array<S8> = Array.new::<S8>(unwind_context_size(), 0 as S8)
    backtraceCursorBuffer: mut Array<S8> = Array.new::<S8>(unwind_cursor_size(), 0 as S8)
    procedureNameBuffer: mut Array<S8> = Array.new::<S8>(256, 0 as S8)
    relativeIpBuffer: mut Array<UWord> = Array.new::<UWord>(1, 0 as UWord)

    private nothrow constructor {}

    export fn create(borrow world: read World) -> own StackTraceCollector = StackTraceCollector()
}

private intrinsic nothrow fn writeMemoryAddress(address: UWord, fd: S32)

private mut fn writeProcedureName(borrow collector: mut StackTraceCollector, cursorPtr: COpaquePointer, fd: S32) {
    errorCode = unw_get_proc_name(cursorPtr, collector.procedureNameBuffer.addressOfFirst(), collector.procedureNameBuffer.size, collector.relativeIpBuffer.addressOfFirst())
    if errorCode == UNWIND_ERROR_SUCCESS {
        // TODO: use safe array access to enable nothrow
        var actualNameLength = 0 as UWord
        while collector.procedureNameBuffer[actualNameLength] != 0 and actualNameLength < collector.procedureNameBuffer.size {
            // TODO: use safe/modular math to enable nothrow
            set actualNameLength = actualNameLength + 1
        }
        write(fd, collector.procedureNameBuffer.addressOfFirst(), actualNameLength)
    } else {
        // TODO: use early return; currently not possible because just "return;" requires a reference to Unit
        replacement = "<unknown function>"
        write(fd, replacement.utf8Data.addressOfFirst(), replacement.utf8Data.size)
    }
}

// prints the stack to FD_STDERR. Is effectively nothrow.
// @return whether the stack could be traced. If false, an error message will be written to FD_STDERR
mut fn printStackTraceToStandardError(borrow collector: mut StackTraceCollector) -> Bool {
    var errorCode = unw_getcontext(collector.backtraceContextBuffer.addressOfFirst())
    if errorCode != UNWIND_ERROR_SUCCESS {
        printError("  !! failed to backtrace; unw_getcontext errored: ")
        printError(unwindErrorToStringSafe(errorCode))
        printError("\n")
        return false
    }

    set errorCode = unw_init_local(collector.backtraceCursorBuffer.addressOfFirst(), collector.backtraceContextBuffer.addressOfFirst())
    if errorCode != UNWIND_ERROR_SUCCESS {
        printError("  !! failed to backtrace; unw_init_local errored: ")
        printError(unwindErrorToStringSafe(errorCode))
        printError("\n")
        return false
    }
    
    couldSkipSelf = unwindCursorTryStepUp(collector.backtraceCursorBuffer.addressOfFirst())
    if not couldSkipSelf {
        printError("  !! failed to backtrace; could not unw_step past the printing infrastructure frames\n")
        return false
    }

    while true {
        ip = unwindCursorGetInstructionPointer(collector.backtraceCursorBuffer.addressOfFirst(), collector.registerBuffer)
        
        printError("  at ")
        writeProcedureName(collector, collector.backtraceCursorBuffer.addressOfFirst(), FD_STDERR)
        printError(" (")
        writeMemoryAddress(ip, FD_STDERR)
        printError(")\n")
        
        hasNext = unwindCursorTryStepUp(collector.backtraceCursorBuffer.addressOfFirst())
        if not hasNext {
            break
        }
    }
    
    return true
}

// not used right now, but might come in handy when implementing actual unwinding/resume

private class UnwindProcedureInfo {
    private addressOfFirstInstruction: UWord = init
    private addressBehindLastInstruction: UWord = init
    private addressOfLanguageSpecificDataArea: UWord = init
    private addressOfPersonalityFunction: UWord = init
    private globalPointer: UWord = init

    private fn fromCursor(cursorPtr: read COpaquePointer) -> own UnwindProcedureInfo {
        // there are additional members in the struct that are not mapped here
        buf = Array.new::<UWord>(8, 0 as UWord)

        errorCode = unw_get_proc_info(cursorPtr, buf.addressOfFirst())
        if errorCode != UNWIND_ERROR_SUCCESS {
            panic("unw_get_proc_info errored: " + unwindErrorToString(errorCode))
        }

        return UnwindProcedureInfo(
            buf[0],
            buf[1],
            buf[2],
            buf[3],
            buf[4]
        )
    }
}