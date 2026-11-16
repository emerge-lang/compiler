package emerge.core.reflection

import emerge.platform.panic

// whether [instance] is an object of the base type [type], or of a subtype of it. What `is` and `as` do for
// types without type arguments.
// `null` is no instance of any base type.
export nothrow fn isInstanceOf(borrow instance: Any?, borrow type: ReflectionBaseType) -> Bool {
    if isNull(instance) {
        return false
    }

    return (instance ?: panic("unreachable")).reflectionBaseType.isSubtypeOf(type)
}

// whether [instance] is a value of [type], type arguments included; `null` is a value of the nullable types.
// What `is` and `as` do for all the other types.
export nothrow fn isInstanceOf(instance: Any?, type: const Type) -> Bool {
    if isNull(instance) {
        return typeOf::<Nothing?>().isSubtypeOf(type)
    }

    return (instance ?: panic("unreachable")).type.isSubtypeOf(type)
}
