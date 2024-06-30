package emerge.platform

// does a best-effort attempt to deliver the message to the user (e.g. send it to STDERR)
// and then kills the ENTIRE process immediately.
// this is declared nothrow because it actually doesn't deal with exceptions internally
// this is declared pure so it can be called from pure contexts, even though it clearly isn't
// but if you're panicking, what use is the side-effect reasoning anyways?
export intrinsic nothrow fn panic(message: String) -> Nothing
