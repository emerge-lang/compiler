package emerge.core

export token class Cell<T> {
    private var _value: T = init

    export nothrow intrinsic get fn value(self: read _) -> T
    export nothrow intrinsic fn update(self: read _, value: T)
}