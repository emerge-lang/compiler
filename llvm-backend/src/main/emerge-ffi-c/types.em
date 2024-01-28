package emerge.ffi.c

struct COpaquePointer {}

struct CPointer<T> {
    pointed: T
}

struct CValue<T> {
    raw: T
}