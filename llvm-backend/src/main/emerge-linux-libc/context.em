package emerge.linux.libc

import emerge.ffi.c.COpaquePointer

external(C) nothrow mut fn setcontext(ctxPtr: COpaquePointer) -> S32
