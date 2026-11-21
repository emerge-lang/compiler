package emerge.std.collections

export interface Map<Key : const Hashable & Equatable<Key>, Value> {
    export operator fn setAtIndex(self: mut _, index: Key, value: Value) -> Value?
    export operator fn getAtIndex(self: mut _, index: Key) -> Value?
    export fun asRange(self) -> SizedRange<out read MapEntry<Key, Value>>
}

export class MapEntry<Key, Value> {
    key: Key = init
    var value: Value = init
}