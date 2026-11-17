package emerge.core

import emerge.core.safemath.plusModulo
import emerge.platform.panic
import emerge.core.utf8.rejectInvalidUtf8

export class String : const NonToken {
    export utf8Data: Array<S8> = init

    private nothrow constructor {}

    // @return a String of the given bytes
    // @throws InvalidUtf8Exception if the bytes are not valid UTF-8
    export fn fromUtf8(capture utf8Data: Array<S8>) -> own String {
        rejectInvalidUtf8(utf8Data)
        return String(utf8Data)
    }

    export nothrow operator fn plus(self, borrow other: read String) -> own String {
        newSize = self.utf8Data.size.plusModulo(other.utf8Data.size)
        if newSize < self.utf8Data.size {
            panic("the concatenated string is too large")
        }

        newData: own Array<S8> = Array.new(newSize, 0 as S8)
        Array.copy(self.utf8Data, 0, newData, 0, self.utf8Data.size)
        Array.copy(other.utf8Data, 0, newData, self.utf8Data.size, other.utf8Data.size)

        // one valid UTF-8 sequence after another is valid UTF-8
        return String(newData)
    }

    export nothrow operator fn equals(self, borrow other: read String) -> Bool {
        // TODO: horribly inefficient. Needs Array::equals.
        if self.utf8Data.size != other.utf8Data.size {
            return false
        }

        return self.startsWith(other)
    }
    
    export nothrow fn startsWith(self, borrow prefix: read String) -> Bool {
        if self.utf8Data.size < prefix.utf8Data.size {
            return false
        }
        
        var index = 0 as UWord
        while index < prefix.utf8Data.size {
            selfByte = self.utf8Data.getOrPanic(index)
            otherByte = prefix.utf8Data.getOrPanic(index)
            if selfByte != otherByte {
                return false
            }

            set index = index.plusModulo(1 as UWord)
        }

        return true
    }
}