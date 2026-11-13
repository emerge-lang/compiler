package emerge.linux.libc

import emerge.ffi.c.COpaquePointer

external(C) nothrow fn setcontext(ctxPtr: COpaquePointer) -> S32
