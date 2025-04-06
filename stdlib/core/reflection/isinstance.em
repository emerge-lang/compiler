package emerge.core.reflection

export nothrow fn isInstanceOf(borrow instance: Any, borrow type: ReflectionBaseType) -> Bool {
    return instance.reflectType().isSubtypeOf(type)
}