package emerge.core.reflection

import emerge.core.safemath.plusModulo

// runtime type information / reflection data on a base type (class or interface)
// TODO: parameterize on type it is reflection on, like java.lang.Class<T> ?
export class ReflectionBaseType {
    // points to all the DYNAMIC ReflectionBaseType infos, except Any
    private supertypes: const Array<ReflectionBaseType> = init

    export canonicalName: String = init

    // for static typeinfos: points at the dynamic version; for dynamic ones: is null
    private dynamicInstance: ReflectionBaseType? = init

    // compares the two by identity; is pure because these objects are some of the
    // few true singletons in the entire language
    private nothrow intrinsic fn isSameObjectAs(self, borrow other: ReflectionBaseType) -> Bool

    export nothrow fn isSubtypeOf(capture self, borrow supertype: ReflectionBaseType) -> Bool {
        selfDynamic = self.dynamicInstance ?: self

        return selfDynamic.isSubtypeOfAssumeDynamic(supertype.dynamicInstance ?: supertype)
    }

    // does is-subtype-of logic, assuming both [self] and [supertype] are the dynamic version of their typeinfo
    // objects (i.e. [dynamicInstance] is `null` on both of them).
    private nothrow fn isSubtypeOfAssumeDynamic(self, borrow supertype: ReflectionBaseType) -> Bool {
        if self.isSameObjectAs(supertype) {
            return true
        }

        if supertype.isSameObjectAs(reflect Any) {
            return true
        }

        if self.isSameObjectAs(reflect Nothing) {
            return true
        }

        var supertypeIndex = 0 as UWord
        while supertypeIndex < self.supertypes.size {
            if supertype.isSameObjectAs(self.supertypes.getOrPanic(supertypeIndex)) {
                return true
            }
            set supertypeIndex = supertypeIndex.plusModulo(1 as UWord)
        }

        return false
    }
}

export nothrow intrinsic fn reflectType(self: Any) -> ReflectionBaseType