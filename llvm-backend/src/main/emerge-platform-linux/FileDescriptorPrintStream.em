package emerge.platform

import emerge.std.io.PrintStream
import emerge.linux.libc.write
import emerge.linux.libc.getErrno
import emerge.ffi.c.addressOfFirst
import emerge.ffi.c.COpaquePointer
import emerge.std.io.IOException
import emerge.std.collections.ArrayList

// declared here so they are initialized before the streams below
FD_STDIN: S32 = 0
FD_STDOUT: S32 = 1
FD_STDERR: S32 = 2

export StandardOut: mut PrintStream = FileDescriptorPrintStream(FD_STDOUT)
export StandardError: mut PrintStream = FileDescriptorPrintStream(FD_STDERR)

class FileDescriptorPrintStream : PrintStream {
    private fd: S32 = init
    
    override fn put(self: mut _, str: String) {
        var bufToWrite: read Array<S8> = str.utf8Data
        while bufToWrite.size > 0 {
            writeResult = pureWrite(self.fd, bufToWrite.addressOfFirst(), bufToWrite.size)
            if writeResult <= 0 {
                throw WriteFailedException(getErrno())
            }

            set bufToWrite = bufToWrite.sliceOrPanic(writeResult.asUWord(), bufToWrite.size)
        }
    }
    
    override fn putEndOfLine(self: mut _) {
        self.put("\n")
    }
}

private intrinsic nothrow fn pureWrite(fd: S32, buf: COpaquePointer, count: UWord) -> SWord

private class WriteFailedException : IOException {
    errno: S32 = init
    
    constructor {
        mixin ThrowableTrait("write(2) failed, errno = " + self.errno.toString())
    }
}