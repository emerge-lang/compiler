package emerge.platform

// The token it takes to read a stack trace: which code called which, and where that code is in memory.
// The runtime holds one per thread, for panics. Other code obtains one from the root.
export token class StackTraceCollector {
    private nothrow constructor {}

    export intrinsic fn create(borrow world: read World) -> own StackTraceCollector
}
