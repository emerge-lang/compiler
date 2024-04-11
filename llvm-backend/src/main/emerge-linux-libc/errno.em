package emerge.linux.libc

import emerge.ffi.c.*

export EAGAIN: Int = 11
export EBADF: Int = 9
export EDESTADDRREQ: Int = 89
export EDQUOT = 122
export EFAULT = 14
export EFBIG = 27
export EINTR = 4
export EINVAL = 22
export EIO = 5
export ENOSPC = 28
export EPERM = 1
export EPIPE = 32

export external(C) fun __errno_location() -> CPointer<Int>

export fun getErrno() -> Int = __errno_location().pointed
