package emerge.std.coresupport

import emerge.core.unwind.StackTraceElement
import emerge.std.io.PrintStream
import emerge.core.reflection.type

export fn printTo(self: Throwable, borrow target: mut PrintStream) {
    target.put(self.type.baseType.canonicalName)
    target.put(": ")
    target.put(self.message ?: "<no message>")
    target.putEndOfLine()

    stackTrace = self.stackTrace
    if isNull(stackTrace) {
        target.put("  ! stack trace not set")
        return
    }
    foreach element in stackTrace!! {
        target.put("  at ")
        element.printTo(target)
        target.putEndOfLine()
    }
}

export fn printTo(self: StackTraceElement, borrow target: mut PrintStream) {
    target.put(self.procedureName)
    target.put(" (")
    self.address.printTo(target)
    target.put(")")
}