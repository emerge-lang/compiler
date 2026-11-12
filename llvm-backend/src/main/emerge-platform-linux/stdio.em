package emerge.platform

import emerge.linux.libc.write
import emerge.ffi.c.addressOfFirst

// for the runtime, which has to report what went wrong while it prints a stack trace
nothrow fn printError(str: String) {
    // TODO: rewrite in terms of PrintStream
    write(FD_STDERR, str.utf8Data.addressOfFirst(), str.utf8Data.size)
}