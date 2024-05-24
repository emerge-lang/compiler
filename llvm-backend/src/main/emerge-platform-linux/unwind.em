package emerge.platform

// these structures are from LLVM-18s libunwind (libunwindh.h)
// this works because right now, emerge classes have a layout identical to that of C structs
// by the virtue of using LLVM and not re-ordering class variables to save space
// this should be denoted ASAP with an attribute like rusts #[repr(C)] or another mechanism
// of telling the compiler about the desired layout of a type

// the nongnu libunwind has a good documentation of the API: https://www.nongnu.org/libunwind/docs.html

UNWIND_ERROR_SUCCESS: S32                     = 0
UNWIND_ERROR_UNSPECIFIED: S32                 = -6540
UNWIND_ERROR_OOM: S32                         = -6541
UNWIND_ERROR_BAD_REGISTER: S32                = -6542
UNWIND_ERROR_READONLY_REGISTER: S32           = -6543 // attempt to write read-only register
UNWIND_ERROR_STOP: S32                        = -6544 // stop unwinding
UNWIND_ERROR_INVALID_INSTRUCTION_POINTER: S32 = -6545
UNWIND_ERROR_BAD_FRAME: S32                   = -6546
UNWIND_ERROR_INVALID: S32                     = -6547 // unsupported operation or bad value
UNWIND_ERROR_UNSUPPORTED_VERSION: S32         = -6548
UNWIND_ERROR_NO_INFO: S32                     = -6549 // no unwind info found
UNWIND_ERROR_CROSSRASIGNING: S32              = -6550 // cross unwind with return address signing

// constants from __libunwind_config.h
// size of unwind contexts
private intrinsic nothrow fn unwind_context_size() -> UWord
// size of unwind cursors
private intrinsic nothrow fn unwind_cursor_size() -> UWord

// initializes the context
// @param context must point to a region of at least [unwind_context_size] size
// @returns an error code
private external(C) read nothrow unw_getcontext(context: COpaquePointer) -> S32

// initializes an unwind cursor
// @param cursor the cursor to initialize; must point to a region of at least [unwind_cursor_size] size
// @param context a cursor that was initialized with [unw_getcontext]
// @returns an error code
private external(C) read nothrow unw_init_local(cursor: COpaquePointer, context: COpaquePointer) -> S32

// advances the cursor to the previous, less deeply nested stack frame / walks up the stack
// @param cursor a cursor previously initialized with [unw_init_local]
// @return a positive value on success, 0 if there are no more stack frames, or a negative value for an error code
private external(C) read nothrow unw_step(cursor: COpaquePointer) -> S32

export read fn collectStackTrace() -> Array<StackTraceFrame> {

}