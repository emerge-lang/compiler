package emerge.ffi.c

// an address, and as such no token: what it takes to read or write the memory there is another matter
export class COpaquePointer : NonToken {
    private pointed: Any = init
}

export class CPointer<T> {
    export pointed: T = init
}