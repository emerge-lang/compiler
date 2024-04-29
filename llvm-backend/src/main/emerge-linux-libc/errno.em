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

export external(C) readonly fun __errno_location() -> CPointer<S32>

export readonly fun getErrno() -> S32 = __errno_location().pointed
