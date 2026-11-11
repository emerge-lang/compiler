package emerge.core.range

// the half-open range of the numbers from start up to, but excluding, endExclusive. Is empty if start >= endExclusive.
// `a..<b` creates one through UWord.rangeToExclusive
export class UWordRange : Iterable<UWord> & SizedRange<UWord> & BidirectionalRange<UWord> & RandomAccessRange<UWord> {
    export var start: UWord = init
    export var endExclusive: UWord = init

    export override get fn size(self) -> UWord {
        if self.isEmpty {
            return 0
        }

        return self.endExclusive - self.start
    }

    export override get fn front(self) -> UWord {
        if self.isEmpty {
            throw EmptyRangeException()
        }

        return self.start
    }

    export override get fn back(self) -> UWord {
        if self.isEmpty {
            throw EmptyRangeException()
        }

        return self.endExclusive - 1
    }

    private get nothrow fn isEmpty(self) = self.start >= self.endExclusive

    export override fn popFront(self: mut _) {
        if self.isEmpty {
            return
        }

        set self.start = self.start + 1
    }

    export override fn popBack(self: mut _) {
        if self.isEmpty {
            return
        }

        set self.endExclusive = self.endExclusive - 1
    }

    export override fn getAtIndex(self, index: UWord) -> UWord {
        if index >= self.size {
            throw EmptyRangeException()
        }

        return self.start + index
    }

    export override fn asRange(capture self) -> own UWordRange = UWordRange(self.start, self.endExclusive)
}
