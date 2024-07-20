package emerge.platform

import emerge.linux.libc.exit
import emerge.platform.StandardOut

export intrinsic nothrow fn panic(message: String) -> Nothing

export intrinsic nothrow fn panic(throwable: Throwable) -> Nothing