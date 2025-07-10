package emerge.core.range

export interface InputRange<T> {
    // returns the current element in the range. If really necessary, does work to obtain that item
    // though this work should be done in [popFront] whenever possible.
    // throws EmptyRangeException if the range is empty.
    export get fn front(self) -> T

    // does work to determine/obtain the next element in the range and mutates the range
    // so that [front] returns that element. Is a noop if empty.
    export fn popFront(self: mut _)
}

export interface BidirectionalRange<T> : InputRange<T> {
    // akin to [front], but returns the last element in the range
    export get fn back(self) -> T

    // akin to [popFront], but moves the end of the range closer to its front
    export fn popBack(self: mut _)
}

// a range that supports `O(1)` random access
export interface RandomAccessRange<T> : InputRange<T> {
    // returns the value in this range at the given index, or throws EmptyRangeException
    // if this is a [SizedRange] and the index is out of bounds
    export fn getAtIndex(self, index: UWord) -> T
}

// a range that is known to be finite
export interface FiniteRange<T> : InputRange<T> {}

// a range with a known size. This implies that popFront can be invoked
// exactly `.size` times before it throws an [EmptyRangeException].
export interface SizedRange<T> : FiniteRange<T> {
    export get fn size(self) -> UWord
}