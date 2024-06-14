package emerge.platform

import emerge.core.StackTraceElement
import emerge.std.collections.ArrayList

intrinsic export read fn collectStackTrace() -> ArrayList<StackTraceElement>