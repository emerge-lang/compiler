package emerge.linux.libc

import emerge.ffi.c.COpaquePointer

external(C) fun write(fd: Int, buf: COpaquePointer, count: uword) -> iword

external(C) fun malloc(nBytes: uword) -> COpaquePointer

external(C) fun free(allocation: COpaquePointer) -> Unit

external(C) fun exit(status: Int) -> Nothing