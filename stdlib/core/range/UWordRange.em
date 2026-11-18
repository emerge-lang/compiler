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

    export operator fn contains(self, value: UWord) -> Bool = value >= self.start and value < self.endExclusive
    export operator fn contains(self, value: U8) -> Bool = self.contains(value.toUWord())
    export operator fn contains(self, value: U16) -> Bool = self.contains(value.toUWord())
    export operator fn contains(self, value: U32) -> Bool = self.contains(value.toUWord())
    export operator fn contains(self, value: U64) -> Bool = value >= self.start.asU64() and value < self.endExclusive.asU64()
    export operator fn contains(self, value: S8) -> Bool = value >= 0 and self.contains(value.asU8().toUWord())
    export operator fn contains(self, value: S16) -> Bool = value >= 0 and self.contains(value.asU16().toUWord())
    export operator fn contains(self, value: S32) -> Bool = value >= 0 and self.contains(value.asU32().toUWord())
    export operator fn contains(self, value: S64) -> Bool {
        if value < 0 {
            return false
        }

        valU64 = value.asU64()
        if valU64 > UWord.max().asU64() {
            return false
        }

        // valU64 is in UWord range, so safe to convert
        return self.contains(valU64.asUWord())
    }
}
