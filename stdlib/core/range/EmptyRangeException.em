package emerge.core.range

export class EmptyRangeException : Throwable {
    export nothrow constructor {
        mixin ThrowableTrait("No more elements")
    }
}