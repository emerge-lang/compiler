package emerge.core

export token class Cell<T> {
    private var _value: T = init

    export intrinsic get fn value(self: read _) -> T
    export intrinsic fn update(self: read _, value: T)
}