package emerge.std.collections

import emerge.platform.panic
import emerge.core.ArrayIndexOutOfBoundsError
import emerge.core.range.Iterable
import emerge.core.range.SizedRange
import emerge.core.range.RandomAccessRange
import emerge.core.range.EmptyRangeException
import emerge.core.range.BidirectionalRange

export class ArrayList<X : Any> : Iterable<X> {
    private var storage: Array<X?> = Array.new::<X?>(20, null)
    private var _size: UWord = 0

    export get fn size(self) -> UWord = self._size

    export fn add(self: mut _, element: X) {
        if self._size >= self.storage.size {
            self.enlarge()
        }
        set self.storage[self._size] = element
        set self._size = self._size + 1
    }

    export operator fn getAtIndex(self, index: UWord) -> X {
        if index >= self._size {
            throw ArrayIndexOutOfBoundsError(index)
        }

        return self.storage[index]!!
    }
    
    export nothrow fn getOrPanic(self, index: UWord) -> X {
        if index >= self._size  {
            panic("arraylist index out of bounds!")
        }
        
        return self.storage.getOrPanic(index) ?: panic("null value shouldn't be present!")
    }

    export override fn asRange(capture self) -> exclusive SizedRange<X> & RandomAccessRange<X> & BidirectionalRange<X> = ArrayListRange::<X>(self)

    private fn enlarge(self: mut _) {
        newStorage: exclusive _ = Array.new::<X?>(self.storage.size * 2, null)
        Array.copy(self.storage, 0, newStorage, 0, self.storage.size)
        set self.storage = newStorage
    }
}

private class ArrayListRange<T : Any> : SizedRange<T> & RandomAccessRange<T> & BidirectionalRange<T> {
    list: read ArrayList<T> = init
    var frontIndex: UWord = 0
    var backIndexPlus1: UWord = self.list.size

    override get fn size(self) = self.backIndexPlus1 - self.frontIndex

    private get fn isEmpty(self) = self.frontIndex >= self.backIndexPlus1 or self.frontIndex >= self.list.size

    override get fn front(self) -> T {
        if self.isEmpty {
            throw EmptyRangeException()
        }

        return self.list.storage[self.frontIndex]!!
    }

    override get fn back(self) -> T {
        if self.isEmpty {
            throw EmptyRangeException()
        }

        return self.list.storage[self.backIndexPlus1 - 1]!!
    }

    override fn popFront(self: mut _) {
        if self.isEmpty {
            return
        }

        set self.frontIndex = self.frontIndex + 1
    }

    override fn popBack(self: mut _) {
        if self.isEmpty {
            return
        }

        set self.backIndexPlus1 = self.backIndexPlus1 - 1
    }

    override fn getAtIndex(self, index: UWord) -> T {
        actualIndex = self.frontIndex + index
        if actualIndex >= self.backIndexPlus1 or actualIndex >= self.list.size {
            throw EmptyRangeException()
        }

        return self.list.getOrPanic(actualIndex)
    }
}