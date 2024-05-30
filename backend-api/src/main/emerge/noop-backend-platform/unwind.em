package emerge.platform

import emerge.core.StackTraceElement
import emerge.std.collections.List

intrinsic export read fn collectStackTrace() -> List<StackTraceElement>