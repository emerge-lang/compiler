package emerge.ffi.c

export class COpaquePointer {
    private pointed: Any = init
}

export class CPointer<T> {
    export pointed: T = init
}