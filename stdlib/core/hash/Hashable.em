package emerge.core.hash

export interface Hashable {
    export fn hashInto(self, borrow state: mut HashState<*>)
}