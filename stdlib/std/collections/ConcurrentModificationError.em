package emerge.std.collections

export class ConcurrentModificationError : Error {
    nothrow constructor {
        mixin ThrowableTrait("a collection was modified while a range was traversing it")
    }
}