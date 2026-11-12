package emerge.core

import emerge.core.range.Iterable
import emerge.core.unwind.collectStackTrace
import emerge.core.unwind.StackTraceElement
import emerge.platform.StackTraceCollector

export interface Throwable {
    export nothrow get fn message(self) -> String?
    
    // on the first invocation of this function, saves information on the stack trace
    // to be later returned from stackTrace
    // called by the throw keyword. Takes no token: it only writes into this object, and what it writes can
    // only be read with a StackTraceCollector
    export fn fillStackTrace(self: mut _)
    
    // @return the stack trace collected on the first call to [fillStackTrace], or `null` if
    // it was never called or didn't succeed
    // TODO: return type Iterable<...>
    // Reading takes a StackTraceCollector: the stack trace tells who called the code that threw, and where
    // that code is in memory. Without the token, a function could behave differently depending on its caller.
    export nothrow fn stackTrace(self, borrow collector: read StackTraceCollector) -> const Iterable<const StackTraceElement>?
}
export interface Error : Throwable {}

// implements boilerplate code for all Throwables; intended to be used
// as a delegation implementation in Throwables.
// implements Error so it can be used in both Error and Exception classes
export class ThrowableTrait : Error {
	private _message: String? = init

    private var _stackTrace: const Iterable<const StackTraceElement>? = null

    export override fn fillStackTrace(self: mut _) {
        set self._stackTrace = self._stackTrace ?: collectStackTrace(3 as U32, false)
    }

    export override nothrow fn stackTrace(self, borrow collector: read StackTraceCollector) -> const Iterable<const StackTraceElement>? {
        return self._stackTrace
    }

    export override nothrow get fn message(self) = self._message
}
