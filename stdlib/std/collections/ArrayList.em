package emerge.std.collections

import emerge.platform.panic

export class ArrayList<X> {
    private var storage: Array<X?> = Array.new::<X?>(20, null)
    private var _size: UWord = 0

    export fn size(self) -> UWord = self._size

    export fn add(self: mut _, element: X) {
        if self._size >= self.storage.size {
            self.enlarge()
        }
        set self.storage[self._size] = element
        set self._size = self._size + 1
    }

    export operator fn `get`(self, index: UWord) -> X {
        if index >= self._size {
            panic("arraylist index out of bounds!")
        }

        return self.storage[index]!!
    }

    private fn enlarge(self: mut _) {
        newStorage: exclusive _ = Array.new::<X?>(self.storage.size * 2, null)
        Array.copy(self.storage, 0, newStorage, 0, self.storage.size)
        set self.storage = newStorage
    }
}