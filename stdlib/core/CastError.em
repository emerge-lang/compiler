package emerge.core

import emerge.core.reflection.ReflectionBaseType
import emerge.platform.collectStackTrace
import emerge.std.collections.ArrayList

class CastError : Error {
    private var stackTrace: const ArrayList<StackTraceElement>? = null

    export override read fn fillStackTrace(self: mut _) {
        set self.stackTrace = self.stackTrace ?: collectStackTrace(2 as U32, false)
    }

    export override nothrow fn getStackTrace(self) -> const ArrayList<StackTraceElement>? {
        return self.stackTrace
    }

    export override nothrow fn getMessage(self) = "The cast failed; the value is not of the expected type."
}