package emerge.linux.libc

import emerge.ffi.c.COpaquePointer

export external(C) mutable fun write(fd: Int, buf: COpaquePointer, count: uword) -> iword

export external(C) fun malloc(nBytes: uword) -> COpaquePointer

export external(C) fun free(allocation: COpaquePointer) -> Unit

export external(C) mutable fun exit(status: Int) -> Nothing
