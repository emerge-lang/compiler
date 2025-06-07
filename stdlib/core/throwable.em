package emerge.core

import emerge.std.io.PrintStream
import emerge.std.collections.ArrayList
import emerge.core.reflection.reflectType
import emerge.platform.collectStackTrace

export interface Throwable : Printable {
    export nothrow get fn message(self) -> String?
    
    // on the first invocation of this function, saves information on the stack trace
    // to be later returned from stackTrace
    // called by the throw keyword, so that user-code doesn't need to
    // deal with the necessary read side-effect of collectStackTrace
    export read fn fillStackTrace(self: mut _)
    
    // @return the stack trace collected on the first call to [fillStackTrace], or `null` if
    // it was never called or didn't succeed
    // TODO: return type Iterable<...>
    export nothrow get fn stackTrace(self) -> const ArrayList<const StackTraceElement>?
}
export interface Error : Throwable {}

// implements boilerplate code for all Throwables; intended to be used
// as a delegation implementation in Throwables.
// implements Error so it can be used in both Error and Exception classes
export class ThrowableTrait : Error & Printable {
	private _message: String? = init

    private var _stackTrace: const ArrayList<const StackTraceElement>? = null

    export override read fn fillStackTrace(self: mut _) {
        set self._stackTrace = self._stackTrace ?: collectStackTrace(2 as U32, false)
    }

    export override nothrow get fn stackTrace(self) -> const ArrayList<const StackTraceElement>? {
        return self._stackTrace
    }

    export override nothrow get fn message(self) = self._message

    export override fn printTo(self, borrow target: mut PrintStream) {
        target.put(self.reflectType().canonicalName)
        target.put(": ")
        target.put(self.message ?: "<no message>")
        target.putEndOfLine()

        stackTrace = self.stackTrace
        if isNull(stackTrace) {
            target.put("  ! stack trace not set")
            return
        }
        var i = 0 as UWord
        while i < stackTrace!!.size() {
            target.put("  at ")
            stackTrace!![i].printTo(target)
            target.putEndOfLine()
            set i = i + 1
        }
    }
}

export class StackTraceElement : Printable {
    export address: UWord = init
    export procedureName: String = init
    
    export override fn printTo(self, borrow target: mut PrintStream) {
        target.put(self.procedureName)
        target.put(" (")
        self.address.printTo(target)
        target.put(")")
    }
}
