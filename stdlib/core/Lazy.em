package emerge.core

export class Lazy<T : const Any?> {
    private initializer: LazyInitializer<T> = init
    private var initialized: Bool = false
    private _value: T? = null

    export intrinsic get fn value(self) -> T
}

/// replace with a function type in Lazy once they exist
export interface LazyInitializer<T : const Any?> : const NonToken {
    export fn computeValue(self: const _) -> T
}