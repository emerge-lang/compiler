package emerge.core

import emerge.core.range.Iterable
import emerge.core.unwind.StackTraceElement
import emerge.platform.StackTraceCollector

export interface Throwable {
    export nothrow get fn message(self) -> String?

    // Stores where this was thrown. `throw` calls this the first time the throwable is thrown, with the stack
    // trace it collected. Any code can set a stack trace, that is no effect; reading it is another matter.
    export fn setStackTrace(self: mut _, capture trace: const Iterable<const StackTraceElement>)

    // @return the stack trace that was set, or `null` if this was never thrown.
    // Takes a StackTraceCollector: the stack trace tells who called the code that threw, and where that code
    // is in memory. Without the token, a function could behave differently depending on its caller.
    export nothrow fn getStackTrace(self, borrow collector: read StackTraceCollector) -> const Iterable<const StackTraceElement>?
}
export interface Error : Throwable {}

// implements boilerplate code for all Throwables; intended to be used
// as a delegation implementation in Throwables.
// implements Error so it can be used in both Error and Exception classes
export class ThrowableTrait : Error {
	private _message: String? = init

    private var _stackTrace: const Iterable<const StackTraceElement>? = null

    export override fn setStackTrace(self: mut _, capture trace: const Iterable<const StackTraceElement>) {
        set self._stackTrace = trace
    }

    export override nothrow fn getStackTrace(self, borrow collector: read StackTraceCollector) -> const Iterable<const StackTraceElement>? {
        return self._stackTrace
    }

    export override nothrow get fn message(self) = self._message
}
