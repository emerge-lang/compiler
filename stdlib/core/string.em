package emerge.core

import emerge.core.safemath.plusModulo
import emerge.core.utf8.rejectInvalidUtf8

export class String {
    export utf8Data: Array<S8> = init
    
    export constructor {
        rejectInvalidUtf8(self.utf8Data)
    }

    export operator fn plus(self, borrow other: read String) -> exclusive String {
        newData: exclusive Array<S8> = Array.new(self.utf8Data.size + other.utf8Data.size, 0 as S8)
        Array.copy(self.utf8Data, 0, newData, 0, self.utf8Data.size)
        Array.copy(other.utf8Data, 0, newData, self.utf8Data.size, other.utf8Data.size)

        return String(newData)
    }

    export nothrow operator fn equals(self, borrow other: read String) -> Bool {
        // TODO: horribly inefficient. Needs Array::equals.
        if self.utf8Data.size != other.utf8Data.size {
            return false
        }

        var index = 0 as UWord
        while index < self.utf8Data.size {
            selfByte = self.utf8Data.getOrPanic(index)
            otherByte = other.utf8Data.getOrPanic(index)
            if selfByte != otherByte {
                return false
            }

            set index = index.plusModulo(1 as UWord)
        }

        return true
    }
}