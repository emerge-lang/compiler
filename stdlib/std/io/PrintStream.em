package emerge.std.io

// TODO: parameterize side-effects
export interface PrintStream {
    export fn put(self: mut _, str: String)
    export fn putEndOfLine(self: mut _)
}