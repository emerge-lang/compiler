package emerge.core.range

import emerge.platform.panic

export class ArrayRange<Element> : SizedRange<Element> & RandomAccessRange<Element> & BidirectionalRange<Element> {
    array: read Array<Element> = init
    var frontIndex: UWord = 0
    var backIndexPlus1: UWord = self.array.size

    export override get fn size(self) = self.backIndexPlus1 - self.frontIndex

    export override get fn front(self) -> Element {
        try {
            return self.array[self.frontIndex]
        } catch e {
            if e is ArrayIndexOutOfBoundsError {
                throw EmptyRangeException()
            }

            throw e
        }
    }

    export override get fn back(self) -> Element {
        try {
            return self.array[self.backIndexPlus1 - 1]
        } catch e {
            if e is ArrayIndexOutOfBoundsError {
                throw EmptyRangeException()
            }

            throw e
        }
    }

    private get fn isEmpty(self) = self.frontIndex >= self.backIndexPlus1 or self.frontIndex >= self.array.size

    export override fn popFront(self: mut _) {
        if self.isEmpty {
            return
        }

        set self.frontIndex = self.frontIndex + 1
    }

    export override fn popBack(self: mut _) {
        if self.isEmpty {
            return
        }

        set self.backIndexPlus1 = self.backIndexPlus1 - 1
    }

    export override fn getAtIndex(self, index: UWord) -> Element {
        actualIndex = self.frontIndex + index
        if actualIndex >= self.backIndexPlus1 or actualIndex >= self.array.size {
            throw EmptyRangeException()
        }

        return self.array.getOrPanic(actualIndex)
    }
}