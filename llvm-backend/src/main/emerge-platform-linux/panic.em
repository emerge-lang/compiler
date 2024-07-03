package emerge.platform

export intrinsic nothrow fn panic(message: String) -> Nothing

// TODO: define in emerge source; needs Display interface
export intrinsic nothrow fn panicOnThrowable(throwable: Throwable) -> Nothing