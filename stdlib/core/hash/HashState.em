package emerge.core.hash

export interface HashState<R> {
    export fn addRaw(self: mut _, borrow v: UWord)
    export get fn hashValue(self) -> R
}
