package emerge.core.unwind

import emerge.core.unwind.StackTraceElement
import emerge.core.range.Iterable

// @param nFramesToSkip skips this amount of frames, e.g. to hide stack of code doing exception handling
// @param stopAtMain if false, excludes frames of the emerge runtime that invoke the programs main function
// Not exported: the result tells who called and where the code is in memory, which takes a StackTraceCollector to
// know. Code outside of this module gets a stack trace by throwing, and reads it through Throwable.stackTrace
intrinsic fn collectStackTrace(nFramesToSkip: U32, includeRuntimeFrames: Bool) -> own Iterable<const StackTraceElement>
