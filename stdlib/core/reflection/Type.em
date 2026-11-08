package emerge.core.reflection

import emerge.platform.panic

// runtime type information on a type (as opposed to ReflectionBaseType, which describes a base type only):
// a base type together with nullability and type arguments, or an intersection of those.
export interface Type {
    // the same type, with the nullability replaced
    export fn withNullability(capture self, nullable: Bool) -> const Type

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

    export override fn withNullability(capture self, nullable: Bool) -> const NamedType {
        if self.nullable == nullable {
            return self
        }
        return NamedType(self.baseType, nullable, self.arguments)
    }

    export override nothrow fn componentCount(self) -> UWord = 1

    export override nothrow fn firstComponent(capture self) -> const NamedType = self

    export override fn toString(self) -> String {
        var str = self.baseType.canonicalName

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

    export override fn withNullability(capture self, nullable: Bool) -> const Type {
        newComponents: exclusive Array<NamedType> = Array.new::<NamedType>(self.components.size, self.components[0])
        foreach i in 0..<self.components.size {
            set newComponents[i] = self.components[i].withNullability(nullable)
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

export class TypeArgument : const Any {
    // one of VARIANCE_INVARIANT, VARIANCE_IN, VARIANCE_OUT
    export variance: U8 = init
    export type: const Type = init

    export fn toString(self) -> String {
        if self.variance == VARIANCE_INVARIANT {
            return self.type.toString()
        }

        if self.variance == VARIANCE_IN {
            return "in " + self.type.toString()
        }

        if self.variance == VARIANCE_OUT {
            return "out " + self.type.toString()
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
export fn intersectionOf(capture components: const Array<const Type>) -> const Type {
    var count: UWord = 0
    foreach component in components {
        set count = count + component.componentCount()
    }

    if count == 1 {
        return components[0]
    }

    flat: exclusive Array<NamedType> = Array.new::<NamedType>(count, components[0].firstComponent())
    var flatIndex: UWord = 0
    foreach component in components {
        if component is IntersectionType {
            foreach nested in (component as IntersectionType).components {
                set flat[flatIndex] = nested
                set flatIndex = flatIndex + 1
            }
        } else {
            set flat[flatIndex] = component as NamedType
            set flatIndex = flatIndex + 1
        }
    }

    return IntersectionType(flat)
}
