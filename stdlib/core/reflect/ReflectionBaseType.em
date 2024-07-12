package emerge.core.reflect

// runtime type information / reflection data on a base type (class or interface)
// TODO: parameterize on type it is reflection on, like java.lang.Class<T> ?
export class ReflectionBaseType {
    private supertypes: const Array<ReflectionBaseType> = init
    export canonicalName: String = init
    private dynamicInstance: ReflectionBaseType? = init
}

export nothrow intrinsic fn reflect(self: Any) -> ReflectionBaseType
export nothrow intrinsic fn reflect<T>() -> ReflectionBaseType