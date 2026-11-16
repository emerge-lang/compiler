package emerge.core.reflection

import emerge.platform.panic
import emerge.core.safemath.plusModulo

// whether [instance] is an object of the base type [type], or of a subtype of it. What `is` and `as` do for
// types without type arguments. `null` is no instance of any base type.
export nothrow fn isInstanceOf(borrow instance: Any?, borrow type: ReflectionBaseType) -> Bool {
    if isNull(instance) {
        return false
    }

    return (instance ?: panic("unreachable")).reflectionBaseType.isSubtypeOf(type)
}

// whether [instance], referred to by a reference of the type [reference], is a value of [type]: of its base
// type, type arguments and mutability. `null` is a value of the nullable types. What `is` and `as` do for all
// types that the other isInstanceOf doesn't do.
//
// An object doesn't know the mutability of the references to it, so that comes from [reference]: the static
// type of the value that is being checked. Of it, only the mutability is used.
export nothrow fn isInstanceOf(instance: Any?, type: const Type, reference: const Type) -> Bool {
    if isNull(instance) {
        return type.isNullable()
    }

    typeOfInstance = (instance ?: panic("unreachable")).type.withMutability(mutabilityOfReference(reference))
    return typeOfInstance.isSubtypeOf(type)
}

// whether `null` is a value of [self]
nothrow fn isNullable(capture self: const Type) -> Bool {
    if self is NamedType {
        return self.asNamedType().nullable
    }

    components = self.asIntersectionType().components
    var index: UWord = 0
    while index < components.size {
        if not components.getOrPanic(index).nullable {
            return false
        }
        set index = index.plusModulo(1 as UWord)
    }

    return true
}
