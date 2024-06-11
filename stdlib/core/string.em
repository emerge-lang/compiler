package emerge.core

export class String {
    export utf8Data: Array<S8> = init

    export mut operator fn plus(self, borrow other: read String) -> exclusive String {
        newData: exclusive Array<S8> = Array.new(self.utf8Data.size + other.utf8Data.size, 0 as S8)
        Array.copy(self.utf8Data, 0, newData, 0, self.utf8Data.size)
        Array.copy(other.utf8Data, 0, newData, self.utf8Data.size, other.utf8Data.size)

        return String(newData)
    }
}