package emerge.platform

import emerge.linux.libc.write
import emerge.ffi.c.addressOfFirst

FD_STDIN: Int = 0
FD_STDOUT: Int = 1
FD_STDERR: Int = 2

export mutable fun print(str: String) {
    write(FD_STDOUT, str.utf8Data.addressOfFirst(), str.utf8Data.size())
}