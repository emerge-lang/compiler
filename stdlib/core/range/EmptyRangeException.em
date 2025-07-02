package emerge.core.range

export class EmptyRangeException : Throwable {
    export constructor {
        mixin ThrowableTrait("No more elements")
    }
}