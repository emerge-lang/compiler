package emerge.core

export interface Equatable<V> {
    export operator fn equals(self, borrow other: read V) -> Bool
}