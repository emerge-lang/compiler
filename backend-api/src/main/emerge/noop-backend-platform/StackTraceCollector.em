package emerge.platform

// Collects stack traces. The runtime holds one per thread, for `throw` and for panics. Other code obtains one
// from the root.
export token class StackTraceCollector {
    private nothrow constructor {}

    export intrinsic fn create(borrow world: read World) -> own StackTraceCollector
}
