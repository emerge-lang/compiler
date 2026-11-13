package emerge.core.unwind

import emerge.core.unwind.StackTraceElement
import emerge.core.range.Iterable
import emerge.platform.StackTraceCollector

// @param nFramesToSkip skips this amount of frames, e.g. to hide stack of code doing exception handling
// @param stopAtMain if false, excludes frames of the emerge runtime that invoke the programs main function
// Takes the token because the result tells who called, and where the code is in memory.
intrinsic export fn collectStackTrace(borrow collector: read StackTraceCollector, nFramesToSkip: U32, includeRuntimeFrames: Bool) -> const Iterable<const StackTraceElement>

// What `throw` does before the throwable propagates; the compiler generates the invocation. It gives the
// throwable its stack trace, unless it has one already (as when it is thrown again).
// Takes no token and is no effect all the same: the stack trace is written into the throwable, and reading it
// from there takes a StackTraceCollector. The runtime uses the one it holds, see fillStackTraceUsing.
intrinsic fn fillStackTraceOnThrow(borrow throwable: mut Throwable)

fn fillStackTraceUsing(borrow throwable: mut Throwable, borrow collector: read StackTraceCollector) {
    if isNull(throwable.getStackTrace(collector)) {
        // skips the frames of this function and of the platform function that walks the stack; the two
        // intrinsics in between are always inlined
        throwable.setStackTrace(collectStackTrace(collector, 2 as U32, false))
    }
}
