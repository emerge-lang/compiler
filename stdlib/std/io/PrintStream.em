package emerge.std.io

// Something text can be written to. Whether an implementation is a token is up to it: a stream to a file
// descriptor is one, a stream that collects the text in memory is not.
export interface PrintStream {
    export fn put(self: mut _, str: String)
    export fn putEndOfLine(self: mut _)
}