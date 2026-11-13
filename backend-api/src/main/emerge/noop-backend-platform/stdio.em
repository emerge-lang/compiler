package emerge.platform

import emerge.std.io.PrintStream

// The standard output of the process. There is one, so there is one instance of this class.
export unique class StandardOut : PrintStream {
    export nothrow constructor {}

    export override intrinsic fn put(self: mut _, str: String)
    export override intrinsic fn putEndOfLine(self: mut _)
}

// The standard error output of the process. There is one, so there is one instance of this class.
export unique class StandardError : PrintStream {
    export nothrow constructor {}

    export override intrinsic fn put(self: mut _, str: String)
    export override intrinsic fn putEndOfLine(self: mut _)
}
