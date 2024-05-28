package emerge.core

// does a best-effort attempt to deliver the message to the user (e.g. send it to STDERR)
// and then stops the process immediately
// todo: remove nothrow as soon as panic actually unwinds the stack, as it should
export intrinsic nothrow fn panic(message: String) -> Nothing
