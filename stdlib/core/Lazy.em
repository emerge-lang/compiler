package emerge.core

/// A value computed on first access. The [initializer] runs at most once successfully; if it throws, the next
/// access runs it again. Accessing [value] from within the initializer is a panic.
export class Lazy<T : const Any?> {
    private initializer: const LazyInitializer<T> = init
    private var initializing: Bool = false
    private var initialized: Bool = false
    private var _value: T? = null

    export intrinsic get fn value(self: read _) -> T
}

/// replace with a function type in Lazy once they exist
export interface LazyInitializer<T : const Any?> : const NonToken {
    export fn computeValue(self: const _) -> T
}
