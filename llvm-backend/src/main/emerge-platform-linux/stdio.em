package emerge.platform

import emerge.linux.libc.write
import emerge.ffi.c.addressOfFirst

val FD_STDIN: Int = 0
val FD_STDOUT: Int = 1
val FD_STDERR: Int = 2

fun print(str: String) {
    write(FD_STDOUT, str.utf8Data.addressOfFirst(), str.utf8Data.size())
}