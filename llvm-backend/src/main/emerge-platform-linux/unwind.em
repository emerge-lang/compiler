package emerge.platform

import emerge.core.StackTraceElement
import emerge.std.collections.ArrayList
import emerge.ffi.c.addressOfFirst
import emerge.ffi.c.COpaquePointer

export mut fn collectStackTrace() -> ArrayList<StackTraceElement> {
    stackList: exclusive _ = ArrayList::<const StackTraceElement>()
    ctx = UnwindContext()
    cursor: mut _ = UnwindCursor(ctx)
    // TODO: do-while
    var hasNext = true
    while hasNext {
        procName = cursor.getProcedureName()

        procInfo = UnwindProcedureInfo.fromCursor(cursor)
        stackList.add(StackTraceElement(procInfo.globalPointer, procName))
        set hasNext = cursor.tryStepUp()
    }

    return stackList
}

// these structures are from LLVM-18s libunwind (libunwindh.h)
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

private fn unwindErrorToString(code: S32) -> String {
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

    return "unknown error (code " + code.toString() + ")"
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

private external(C) nothrow fn unw_get_proc_name(cursor: COpaquePointer, buf: COpaquePointer, len: UWord, offp: COpaquePointer) -> S32

private external(C) nothrow fn unw_get_proc_info(cursor: COpaquePointer, buf: COpaquePointer) -> S32

private class UnwindContext {
    private buffer = Array.new::<S8>(unwind_context_size(), 0 as S8)

    read constructor {
        errorCode = unw_getcontext(self.buffer.addressOfFirst())
        if errorCode != UNWIND_ERROR_SUCCESS {
            panic("unw_getcontext errored: " + unwindErrorToString(errorCode))
        }
    }

    private fn ref(self: read _) -> COpaquePointer {
        return self.buffer.addressOfFirst()
    }
}

private class UnwindCursor {
    private context: UnwindContext = init
    private buffer = Array.new::<S8>(unwind_cursor_size(), 0 as S8)

    read constructor {
        errorCode = unw_init_local(self.buffer.addressOfFirst(), self.context.ref())
        if errorCode != UNWIND_ERROR_SUCCESS {
            panic("unw_init_local errored: " + unwindErrorToString(errorCode))
        }
    }

    private fn ref(self: read _) -> COpaquePointer {
        return self.buffer.addressOfFirst()
    }

    // attempts to move the cursor to the next, less deeply nested tack frame
    // @return true if the cursor was successfully moved, false if there are no more stack frames left
    private read fn tryStepUp(self: mut _) -> Bool {
        errorCode = unw_step(self.ref())
        if errorCode == UNWIND_ERROR_STOP or errorCode == 0 {
            return false
        }

        if errorCode < 0 {
            panic("unw_step errored: " + unwindErrorToString(errorCode))
        }

        return true
    }

    // returns the name of the function belonging to the stack frame this cursor is currently pointing at
    private fn getProcedureName(self) -> String {
        var nameBuf = Array.new::<S8>(256, 0 as S8)
        offpBuf = Array.new::<UWord>(1, 0 as UWord)

        errorCode = unw_get_proc_name(self.ref(), nameBuf.addressOfFirst(), nameBuf.size, offpBuf.addressOfFirst())
        if errorCode != UNWIND_ERROR_SUCCESS {
            panic("unw_get_proc_name errored: " + unwindErrorToString(errorCode))
        }

        var actualNameLength = 0 as UWord
        while nameBuf[actualNameLength] == 0 and actualNameLength < nameBuf.size {
            set actualNameLength = actualNameLength + 1
        }

        trimmedName: exclusive _ = Array.new::<S8>(actualNameLength, 0 as S8)
        Array.copy(nameBuf, 0, trimmedName, 0, actualNameLength)
        return String(trimmedName)
    }
}

private class UnwindProcedureInfo {
    private addressOfFirstInstruction: UWord = init
    private addressBehindLastInstruction: UWord = init
    private addressOfLanguageSpecificDataArea: UWord = init
    private addressOfPersonalityFunction: UWord = init
    private globalPointer: UWord = init

    private fn fromCursor(cursor: UnwindCursor) -> exclusive UnwindProcedureInfo {
        // there are additional members in the struct that are not mapped here
        buf = Array.new::<UWord>(8, 0 as UWord)

        errorCode = unw_get_proc_info(cursor.ref(), buf.addressOfFirst())
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