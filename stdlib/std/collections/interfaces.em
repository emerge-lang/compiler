package emerge.std.collections

import emerge.core.range.SizedRange

export interface Map<Key : const Equatable<Key>, Value> {
    export operator fn setAtIndex(self: mut _, index: Key, value: Value) -> Value?
    export operator fn getAtIndex(self: mut _, borrow index: Key) -> Value?
    export operator fn remove(self: mut _, borrow key: Key) -> Value?
    export operator fn contains(self, borrow key: Key) -> Bool 
    export fn asRange(self) -> SizedRange<out read MapEntry<Key, Value>>
    export fn size(self) -> UWord
}

export class MapEntry<Key, Value> {
    key: Key = init
    var value: Value = init
}

export interface Set<Element : const Equatable<Element>> {
    export operator fn contains(self, borrow element: Element) -> Bool
    export operator fn add(self: mut _, element: Element) -> Bool
    export operator fn remove(self: mut _, borrow element: Element) -> Bool
}