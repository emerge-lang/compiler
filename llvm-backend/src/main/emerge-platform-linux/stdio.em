package emerge.platform

import emerge.linux.libc.write
import emerge.ffi.c.addressOfFirst

FD_STDIN: S32 = 0
FD_STDOUT: S32 = 1
FD_STDERR: S32 = 2

export mut fn print(str: String) {
    write(FD_STDOUT, str.utf8Data.addressOfFirst(), str.utf8Data.size)
}