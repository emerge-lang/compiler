package emerge.core

import emerge.core.range.Iterable
import emerge.core.reflection.reflectType
import emerge.core.unwind.collectStackTrace
import emerge.core.unwind.StackTraceElement

export interface Throwable {
    export nothrow get fn message(self) -> String?
    
    // on the first invocation of this function, saves information on the stack trace
    // to be later returned from stackTrace
    // called by the throw keyword, so that user-code doesn't need to
    // deal with the necessary read side-effect of collectStackTrace
    export read fn fillStackTrace(self: mut _)
    
    // @return the stack trace collected on the first call to [fillStackTrace], or `null` if
    // it was never called or didn't succeed
    // TODO: return type Iterable<...>
    export nothrow get fn stackTrace(self) -> const Iterable<const StackTraceElement>?
}
export interface Error : Throwable {}

// implements boilerplate code for all Throwables; intended to be used
// as a delegation implementation in Throwables.
// implements Error so it can be used in both Error and Exception classes
export class ThrowableTrait : Error {
	private _message: String? = init

    private var _stackTrace: const Iterable<const StackTraceElement>? = null

    export override read fn fillStackTrace(self: mut _) {
        set self._stackTrace = self._stackTrace ?: collectStackTrace(3 as U32, false)
    }

    export override nothrow get fn stackTrace(self) -> const Iterable<const StackTraceElement>? {
        return self._stackTrace
    }

    export override nothrow get fn message(self) = self._message
}
