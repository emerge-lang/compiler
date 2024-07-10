package emerge.std

import emerge.std.io.PrintStream

export interface Printable {
    export fn printTo(self, borrow stream: mut PrintStream)
}