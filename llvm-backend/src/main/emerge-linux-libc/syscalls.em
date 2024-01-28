package emerge.linux.libc

import emerge.ffi.c.COpaquePointer

external(C) fun write(fd: Int, buf: COpaquePointer, count: uword) -> iword