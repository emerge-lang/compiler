package emerge.core

export class Weak<T : Any> {
    private value: T = init

    export constructor {}

    export intrinsic fn toStrongOrNull(self) -> T?
}