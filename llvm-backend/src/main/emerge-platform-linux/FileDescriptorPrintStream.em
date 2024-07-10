package emerge.platform

import emerge.std.io.PrintStream
import emerge.linux.libc.write
import emerge.linux.libc.getErrno
import emerge.ffi.c.addressOfFirst
import emerge.ffi.c.COpaquePointer

StandardOut: mut PrintStream = FileDescriptorPrintStream(FD_STDOUT)
StandardError: mut PrintStream = FileDescriptorPrintStream(FD_STDERR)

class FileDescriptorPrintStream : PrintStream {
    private fd: S32 = init
    
    override fn put(self: mut _, str: String) {
        var bufToWrite: read Array<S8> = str.utf8Data
        var nBytesWritten = 0 as UWord
        while nBytesWritten < str.utf8Data.size {
            writeResult = pureWrite(self.fd, bufToWrite.addressOfFirst(), bufToWrite.size)
            if writeResult <= 0 {
                // TODO: raise IOException
                // TODO: include errno, once PrintStream.toString is implemented
                panic("write errored")
            }
            set nBytesWritten = nBytesWritten + writeResult.asUWord()
        }
    }
    
    override fn putEndOfLine(self: mut _) {
        self.put("\n")
    }
}

private intrinsic nothrow fn pureWrite(fd: S32, buf: COpaquePointer, count: UWord) -> SWord