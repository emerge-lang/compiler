package emerge.platform

import emerge.linux.libc.exit
import emerge.platform.StandardOut

export intrinsic nothrow fn panic(message: String) -> Nothing

// TODO: define in emerge source; needs Display interface
export intrinsic nothrow fn panicOnThrowable(throwable: Throwable) -> Nothing

private mut nothrow fn panicOnThrowableImpl(throwable: Throwable) -> Nothing {
    // TODO: actually print the throwable, needs try+catch
    return panic(throwable.getMessage() ?: "<no message>")
}