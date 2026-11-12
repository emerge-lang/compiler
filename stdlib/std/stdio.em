package emerge.std

import emerge.std.io.PrintStream

// writes [str] and an end of line to this stream
export fn println(self: mut PrintStream, str: String) {
    self.put(str)
    self.putEndOfLine()
}
