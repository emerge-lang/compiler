package emerge.linux.libc

import emerge.ffi.c.COpaquePointer

export external(C) mut fn write(fd: S32, buf: COpaquePointer, count: UWord) -> SWord

export external(C) fn malloc(nBytes: UWord) -> COpaquePointer

export external(C) fn free(allocation: COpaquePointer) -> Unit

export external(C) mut fn exit(status: S32) -> Nothing
