package emerge.linux.libc

import emerge.ffi.c.COpaquePointer

export external(C) mutable fun write(fd: S32, buf: COpaquePointer, count: UWord) -> SWord

export external(C) fun malloc(nBytes: UWord) -> COpaquePointer

export external(C) fun free(allocation: COpaquePointer) -> Unit

export external(C) mutable fun exit(status: S32) -> Nothing
