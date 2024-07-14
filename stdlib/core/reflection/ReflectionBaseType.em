package emerge.core.reflection

// runtime type information / reflection data on a base type (class or interface)
// TODO: parameterize on type it is reflection on, like java.lang.Class<T> ?
export class ReflectionBaseType {
    private supertypes: const Array<ReflectionBaseType> = init
    export canonicalName: String = init
    private dynamicInstance: ReflectionBaseType? = init
}

export nothrow intrinsic fn reflectType(self: Any) -> ReflectionBaseType