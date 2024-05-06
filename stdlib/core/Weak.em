package emerge.core

export class Weak<T : Any> {
    private value: T = init

    export constructor {}

    export fn toStrongOrNull(self) -> T? = self.value
}