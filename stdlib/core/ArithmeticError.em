package emerge.core

import emerge.std.collections.ArrayList
import emerge.core.StackTraceElement
import emerge.platform.collectStackTrace

export class ArithmeticError : Error {
    message: String = init

    private var stackTrace: const ArrayList<StackTraceElement>? = null

    export override read fn fillStackTrace(self: mut _) {
        set self.stackTrace = self.stackTrace ?: collectStackTrace(2 as U32, false)
    }

    export override nothrow fn getStackTrace(self) -> const ArrayList<StackTraceElement>? {
        return self.stackTrace
    }

    export override nothrow fn getMessage(self) = self.message
}