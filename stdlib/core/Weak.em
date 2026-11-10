package emerge.core

export class Weak<T : Any> {
    private value: T = init

    export nothrow constructor {}

    export nothrow intrinsic fn toStrongOrNull(self) -> T?
}