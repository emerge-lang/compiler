package emerge.core.reflection

import emerge.core.safemath.plusModulo

// runtime type information / reflection data on a base type (class or interface)
// TODO: parameterize on type it is reflection on, like java.lang.Class<T> ?
export class ReflectionBaseType {
    // points to all the DYNAMIC ReflectionBaseType infos, except Any
    private supertypes: const Array<ReflectionBaseType> = init

    export canonicalName: String = init

    // whether all references to objects of this type are immutable, whatever mutability they are written with
    export isConst: Bool = init

    // whether no object of this type is a token: it is a class that is not declared `token`, or it inherits from
    // NonToken. Such a type is a subtype of NonToken, without having it among [supertypes]. An object of it can
    // still hold a token, where a type argument allows for one: see Type.mayBeToken
    export isNonToken: Bool = init

    // whether this is a class, as opposed to an interface: it has no subtypes but Nothing
    export isClass: Bool = init

    // the supertypes that have type parameters, the indirect ones included, as seen from this type:
    // for `class Nest<E> : Seq<Box<E>>` that is `Seq<Box<#0>>`, where #0 is a TypeParameterPlaceholder
    // for `E`. Shared by the static and the dynamic typeinfo.
    private supertypeTemplates: const Array<NamedType> = init

    // There are two typeinfo objects for each class: static objects (e.g. string literals) refer to one of their
    // own. This gives the one that the other objects refer to; for the typeinfos of interfaces, it is [self].
    private nothrow intrinsic fn dynamicInstance(self) -> ReflectionBaseType

    // compares the two by identity; that tells nothing about where they are in memory, so it takes no
    // AddressSpace. These objects are some of the few true singletons in the entire language
    private nothrow intrinsic fn isSameObjectAs(self, borrow other: ReflectionBaseType) -> Bool

    export nothrow fn isSubtypeOf(capture self, borrow supertype: ReflectionBaseType) -> Bool {
        return self.dynamicInstance().isSubtypeOfAssumeDynamic(supertype.dynamicInstance())
    }

    // whether [self] and [other] describe the same base type
    nothrow fn isSameAs(capture self, borrow other: ReflectionBaseType) -> Bool {
        return self.dynamicInstance().isSameObjectAs(other.dynamicInstance())
    }

    // @return [supertype] as a supertype of this type, from [supertypeTemplates]; `null` if [supertype] has no
    // type parameters, or is no supertype of this type
    nothrow fn supertypeTemplateFor(capture self, borrow supertype: ReflectionBaseType) -> const NamedType? {
        var index = 0 as UWord
        while index < self.supertypeTemplates.size {
            template = self.supertypeTemplates.getOrPanic(index)
            if template.baseType.isSameAs(supertype) {
                return template
            }
            set index = index.plusModulo(1 as UWord)
        }

        return null
    }

    // does is-subtype-of logic, assuming both [self] and [supertype] are the dynamic version of their typeinfo
    // objects (see [dynamicInstance]).
    private nothrow fn isSubtypeOfAssumeDynamic(self, borrow supertype: ReflectionBaseType) -> Bool {
        if self.isSameObjectAs(supertype) {
            return true
        }

        if supertype.isSameObjectAs(typeOf::<Any>().firstComponent().baseType) {
            return true
        }

        if self.isSameObjectAs(typeOf::<Nothing>().firstComponent().baseType) {
            return true
        }

        if supertype.isSameObjectAs(typeOf::<NonToken>().firstComponent().baseType) {
            // classes are below NonToken without saying so
            return self.isNonToken
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

export intrinsic nothrow get fn reflectionBaseType(self: Any) -> ReflectionBaseType