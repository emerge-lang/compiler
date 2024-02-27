package emerge.linux.libc

import emerge.ffi.c.*

EAGAIN: Int = 11
EBADF: Int = 9
EDESTADDRREQ: Int = 89
EDQUOT = 122
EFAULT = 14
EFBIG = 27
EINTR = 4
EINVAL = 22
EIO = 5
ENOSPC = 28
EPERM = 1
EPIPE = 32

external(C) fun __errno_location() -> CPointer<Int>

fun getErrno() -> Int = __errno_location().pointed