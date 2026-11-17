package emerge.core

import emerge.core.reflection.Type
import emerge.platform.panic

class CastError : Error {
    // the type of the value that was cast, with the mutability of the reference it was cast through;
    // null if the value was null
    actualType: const Type? = init
    // the type the value was cast to
    expectedType: const Type = init

    nothrow constructor {
        // cannot use cast here because that would create an infinite loop in the compiler; and even if not,
        // it would "risk" creating an infinite loop at runtime when a CastError cannot be created due to a CastError.
        // The same goes for everything that builds the message.
        mixin ThrowableTrait(castErrorMessage(self.actualType, self.expectedType))
    }
}

private nothrow fn castErrorMessage(actualType: const Type?, expectedType: const Type) -> String {
    if isNull(actualType) {
        return "Cannot cast null to " + expectedType.toString()
    }

    return "Cannot cast a value of type " + (actualType ?: panic("unreachable")).toString() + " to " + expectedType.toString()
}
