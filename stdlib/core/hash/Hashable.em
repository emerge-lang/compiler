package emerge.core.hash

export interface Hashable {
    export fn hashInto(self, borrow state: mut HashState<*>)
}

export fn add(self: mut HashState<*>, borrow v: Hashable) {
    v.hashInto(self)
}