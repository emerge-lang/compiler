package emerge.core

import emerge.std.io.PrintStream
import emerge.std.collections.ArrayList

export interface Throwable : Printable {
    // TODO: make into virtual property
    export nothrow fn getMessage(self) -> String?
    
    // called by the throw keyword, so that user-code doesn't need to 
    // deal with the necessary read side-effect of collectStackTrace
    // TODO: make into fillStackTrace. Is called by the runtime, and it is not always 100% clear whether
    // the exception already has a stacktrace.
    export nothrow fn setStackTrace(self: mut _, trace: const ArrayList<StackTraceElement>)
    
    // TODO: make into virtual property
    // TODO: return type Iterable<...>
    // TODO: return type nullable, let runtime handle missing stacktrace gracefully
    export nothrow fn getStackTrace(self) -> const ArrayList<StackTraceElement>

    export override fn printTo(self, borrow target: mut PrintStream) {
        // TODO: include type name
        target.put(self.getMessage() ?: "<no message>")
        target.putEndOfLine()
        
        stackTrace = self.getStackTrace()
        var i = 0 as UWord
        while i < stackTrace.size() {
            stackTrace[i].printTo(target)
            target.putEndOfLine()
            set i = i + 1
        }
    }
}
export interface Error : Throwable {}

export class StackTraceElement : Printable {
    export address: UWord = init
    export procedureName: String = init
    
    export override fn printTo(self, borrow target: mut PrintStream) {
        target.put("  at ")
        target.put(self.procedureName)
        target.put(" (")
        self.address.printTo(target)
        target.put(")")
    }
}
