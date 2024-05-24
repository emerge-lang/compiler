package emerge.platform

// does a best-effort attempt to deliver the message to the user (e.g. send it to STDERR)
// and then stops the process immediately
export nothrow intrinsic fn panic(message: String) -> Nothing
