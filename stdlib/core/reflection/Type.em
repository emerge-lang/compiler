package emerge.core.reflection

import emerge.platform.panic
import emerge.core.safemath.plusModulo

// runtime type information on a type (as opposed to ReflectionBaseType, which describes a base type only):
// a base type together with nullability and type arguments, or an intersection of those.
export interface Type {
    // the same type, with the nullability replaced
    export nothrow fn withNullability(capture self, nullable: Bool) -> const Type

    // the number of named types this type is composed of: 1 for a NamedType, the number of components for an IntersectionType
    export nothrow fn componentCount(self) -> UWord

    // the first of the named types this type is composed of
    export nothrow fn firstComponent(capture self) -> const NamedType

    export fn toString(self) -> String
}

export class NamedType : const Type {
    export baseType: ReflectionBaseType = init
    export nullable: Bool = init
    export arguments: const Array<TypeArgument> = init

    export override nothrow fn withNullability(capture self, nullable: Bool) -> const NamedType {
        if self.nullable == nullable {
            return self
        }
        return NamedType(self.baseType, nullable, self.arguments)
    }

    export override nothrow fn componentCount(self) -> UWord = 1

    export override nothrow fn firstComponent(capture self) -> const NamedType = self

    export override fn toString(self) -> String {
        bt = self.baseType
        var str = bt.canonicalName

        if self.arguments.size > 0 {
            set str = str + "<" + self.arguments[0].toString()
            foreach a in self.arguments[1..<$] {
                set str = str + ", " + a.toString()
            }
            set  str = str + ">"
        }

        if self.nullable {
            set str = str + "?"
        }

        return str
    }
}

export class IntersectionType : const Type {
    // at least two
    export components: const Array<NamedType> = init

    export override nothrow fn withNullability(capture self, nullable: Bool) -> const Type {
        newComponents: own Array<NamedType> = Array.new::<NamedType>(self.components.size, self.components.getOrPanic(0))
        var index: UWord = 0
        while index < self.components.size {
            newComponents.setOrPanic(index, self.components.getOrPanic(index).withNullability(nullable))
            set index = index.plusModulo(1 as UWord)
        }
        return IntersectionType(newComponents)
    }

    export override nothrow fn componentCount(self) -> UWord = self.components.size

    export override nothrow fn firstComponent(capture self) -> const NamedType = self.components.getOrPanic(0)

    export override fn toString(self) -> String {
        var str = self.components[0].toString()
        foreach c in self.components[1..<$] {
            set str = str + " & " + c.toString()
        }

        return str
    }
}

// stands for a type parameter of a base type in the templates of its supertypes, see
// ReflectionBaseType.supertypeTemplates. Never is the type of a value, and never leaves this package.
class TypeParameterPlaceholder : const Type {
    // the index of the type parameter in the type parameters of the base type
    index: UWord = init
    // one of PLACEHOLDER_NULLABILITY_OF_ARGUMENT (`T`), PLACEHOLDER_NULLABLE (`T?`), PLACEHOLDER_NOT_NULLABLE (`T!`)
    nullability: U8 = init

    override nothrow fn withNullability(capture self, nullable: Bool) -> const Type {
        panic("a type parameter placeholder is not a type")
    }

    override nothrow fn componentCount(self) -> UWord = 1

    override nothrow fn firstComponent(capture self) -> const NamedType {
        panic("a type parameter placeholder is not a type")
    }

    override fn toString(self) -> String = "<type parameter>"

    // @return the type that stands in the place of this placeholder when [argument] is the type argument
    nothrow fn applyNullabilityTo(self, capture argument: const Type) -> const Type {
        if self.nullability == PLACEHOLDER_NULLABILITY_OF_ARGUMENT {
            return argument
        }

        return argument.withNullability(self.nullability == PLACEHOLDER_NULLABLE)
    }
}

PLACEHOLDER_NULLABILITY_OF_ARGUMENT: U8 = 0
PLACEHOLDER_NULLABLE: U8 = 1
PLACEHOLDER_NOT_NULLABLE: U8 = 2

// an intersection in the template of a supertype, with at least one component that mentions a type parameter
// of the base type; see ReflectionBaseType.supertypeTemplates. Like TypeParameterPlaceholder, it never is the
// type of a value.
class IntersectionTemplate : const Type {
    components: const Array<const Type> = init

    override nothrow fn withNullability(capture self, nullable: Bool) -> const Type {
        panic("an intersection template is not a type")
    }

    override nothrow fn componentCount(self) -> UWord = self.components.size

    override nothrow fn firstComponent(capture self) -> const NamedType {
        panic("an intersection template is not a type")
    }

    override fn toString(self) -> String = "<intersection template>"
}

export class TypeArgument : const Any {
    // one of VARIANCE_INVARIANT, VARIANCE_IN, VARIANCE_OUT
    export variance: U8 = init
    export value: const Type = init

    export fn toString(self) -> String {
        if self.variance == VARIANCE_INVARIANT {
            return self.value.toString()
        }

        if self.variance == VARIANCE_IN {
            return "in " + self.value.toString()
        }

        if self.variance == VARIANCE_OUT {
            return "out " + self.value.toString()
        }

        panic("invalid type argument")
    }
}

// TODO: make this a proper enum / union type ones these are implemented
export VARIANCE_INVARIANT: U8 = 0
export VARIANCE_IN: U8 = 1
export VARIANCE_OUT: U8 = 2

// the runtime type information for the type argument. Type parameters are reified, so this works for type
// parameters of the enclosing function or class, too: `typeOf::<T>()`
export nothrow intrinsic fn typeOf<T>() -> const Type

// the intersection of the given types; nested intersections are flattened
export nothrow fn intersectionOf(capture components: const Array<const Type>) -> const Type {
    var count: UWord = 0
    var index: UWord = 0
    while index < components.size {
        set count = count.plusModulo(components.getOrPanic(index).componentCount())
        set index = index.plusModulo(1 as UWord)
    }

    if count == 1 {
        return components.getOrPanic(0)
    }

    flat: own Array<NamedType> = Array.new::<NamedType>(count, components.getOrPanic(0).firstComponent())
    var flatIndex: UWord = 0
    set index = 0
    while index < components.size {
        component = components.getOrPanic(index)
        if component is IntersectionType {
            nested = component.asIntersectionType().components
            var nestedIndex: UWord = 0
            while nestedIndex < nested.size {
                flat.setOrPanic(flatIndex, nested.getOrPanic(nestedIndex))
                set flatIndex = flatIndex.plusModulo(1 as UWord)
                set nestedIndex = nestedIndex.plusModulo(1 as UWord)
            }
        } else {
            flat.setOrPanic(flatIndex, component.asNamedType())
            set flatIndex = flatIndex.plusModulo(1 as UWord)
        }
        set index = index.plusModulo(1 as UWord)
    }

    return IntersectionType(flat)
}

// The casts of this package, for code that is nothrow and knows what it has: `as` throws, so nothrow code cannot use it

nothrow fn asNamedType(capture self: const Type) -> const NamedType {
    return (self as? NamedType) ?: panic("not a NamedType")
}

nothrow fn asIntersectionType(capture self: const Type) -> const IntersectionType {
    return (self as? IntersectionType) ?: panic("not an IntersectionType")
}

nothrow fn asTypeParameterPlaceholder(capture self: const Type) -> const TypeParameterPlaceholder {
    return (self as? TypeParameterPlaceholder) ?: panic("not a TypeParameterPlaceholder")
}

nothrow fn asIntersectionTemplate(capture self: const Type) -> const IntersectionTemplate {
    return (self as? IntersectionTemplate) ?: panic("not an IntersectionTemplate")
}

export nothrow intrinsic get fn type(self: Any) -> NamedType