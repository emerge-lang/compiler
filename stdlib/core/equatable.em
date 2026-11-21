package emerge.core

export interface Equatable<V> {
    export fn equals(self, borrow other: read V) -> Bool
}