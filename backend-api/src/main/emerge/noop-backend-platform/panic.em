package emerge.platform

import emerge.core.Throwable

// does a best-effort attempt to deliver the message to the user (e.g. send it to STDERR)
// and then kills the ENTIRE process immediately.
// this is declared nothrow because it actually doesn't deal with exceptions internally
// it takes no token, even though it clearly has an effect: the runtime holds what it needs,
// and if you're panicking, what use is the reasoning about effects anyways?
export intrinsic nothrow fn panic(message: String) -> Nothing

export intrinsic nothrow fn panic(throwable: Throwable) -> Nothing