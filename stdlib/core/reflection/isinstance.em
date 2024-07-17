package emerge.core.reflection

export nothrow fn isInstanceOf(instance: Any, type: ReflectionBaseType) -> Bool {
    return instance.reflectType().isSubtypeOf(type)
}