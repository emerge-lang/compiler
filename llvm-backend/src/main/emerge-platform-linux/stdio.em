package emerge.platform

import emerge.linux.libc.write
import emerge.ffi.c.addressOfFirst

export mut nothrow fn print(str: String) {
    // TODO: rewrite in terms of PrintStream
    write(FD_STDOUT, str.utf8Data.addressOfFirst(), str.utf8Data.size)
}

export mut nothrow fn printError(str: String) {
    // TODO: rewrite in terms of PrintStream
    write(FD_STDERR, str.utf8Data.addressOfFirst(), str.utf8Data.size)
}