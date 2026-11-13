package emerge.platform

import emerge.linux.libc.write
import emerge.ffi.c.addressOfFirst

// for the runtime, which has to report what went wrong while it prints a stack trace during a panic.
// It writes to the file descriptor directly, and not through a PrintStream: that code must not throw and must
// not allocate, as it also runs when no memory is left.
nothrow fn printError(str: String) {
    write(FD_STDERR, str.utf8Data.addressOfFirst(), str.utf8Data.size)
}