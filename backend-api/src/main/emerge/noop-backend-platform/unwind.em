package emerge.platform

import emerge.core.StackTraceElement
import emerge.std.collections.ArrayList

intrinsic export read fn collectStackTrace() -> exclusive ArrayList<const StackTraceElement>

// @param nFramesToSkip skips this amount of frames, e.g. to hide stack of code doing exception handling
// @param stopAtMain if false, excludes frames of the emerge runtime that invoke the programs main function
intrinsic export read fn collectStackTrace(nFramesToSkip: U32, includeRuntimeFrames: Bool) -> exclusive ArrayList<const StackTraceElement>