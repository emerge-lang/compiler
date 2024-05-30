package emerge.std.collections

export interface List<T> {
    export fn size(self) -> UWord
    export fn add(self: mut _, element: T)
    export operator fn get(index: UWord) -> T
    export operator fn set(index: UWord, element: T)
}