package emerge.core

import emerge.core.reflection.ReflectionBaseType
import emerge.std.collections.ArrayList

class CastError : Error {
    constructor {
        // cannot use cast here because that would create an infinite loop in the compiler; and even if not,
        // it would "risk" creating an infinite loop at runtime when a CastError cannot be created due to a CastError
        mixin ThrowableTrait("The cast failed; the value is not of the expected type.")
    }
}