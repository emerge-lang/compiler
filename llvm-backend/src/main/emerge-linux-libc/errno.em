package emerge.linux.libc

import emerge.ffi.c.*

export EAGAIN: S32 = 11
export EBADF: S32 = 9
export EDESTADDRREQ: S32 = 89
export EDQUOT = 122
export EFAULT = 14
export EFBIG = 27
export EINTR = 4
export EINVAL = 22
export EIO = 5
export ENOSPC = 28
export EPERM = 1
export EPIPE = 32

// TODO: make __errno_location and getErrno read
// this requires some unsafe-style facility to make the compiler accept invocations to read fns in pure contexts
export external(C) nothrow fn __errno_location() -> CPointer<S32>

export nothrow fn getErrno() -> S32 = __errno_location().pointed
