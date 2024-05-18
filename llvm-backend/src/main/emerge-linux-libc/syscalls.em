package emerge.linux.libc

import emerge.ffi.c.COpaquePointer

export external(C) nothrow mut fn write(fd: S32, buf: COpaquePointer, count: UWord) -> SWord

export external(C) nothrow fn malloc(nBytes: UWord) -> COpaquePointer

export external(C) nothrow fn free(allocation: COpaquePointer) -> Unit

export external(C) nothrow mut fn exit(status: S32) -> Nothing
