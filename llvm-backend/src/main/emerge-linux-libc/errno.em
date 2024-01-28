package emerge.linux.libc

import emerge.ffi.c.*

val EAGAIN: Int = 11
val EBADF: Int = 9
val EDESTADDRREQ: Int = 89
val EDQUOT = 122
val EFAULT = 14
val EFBIG = 27
val EINTR = 4
val EINVAL = 22
val EIO = 5
val ENOSPC = 28
val EPERM = 1
val EPIPE = 32

external(C) fun __errno_location() -> CPointer<Int>

fun getErrno() -> Int = __errno_location().pointed