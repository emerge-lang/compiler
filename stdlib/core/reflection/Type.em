package emerge.core.reflection

// runtime type information on a type (as opposed to ReflectionBaseType, which describes a base type only):
// a base type together with nullability and type arguments, or an intersection of those.
export interface Type {
    // the same type, with the nullability replaced
    export fn withNullability(capture self, nullable: Bool) -> const Type

    // the number of named types this type is composed of: 1 for a NamedType, the number of components for an IntersectionType
    export fn componentCount(self) -> UWord

    // the first of the named types this type is composed of
    export fn firstComponent(capture self) -> const NamedType
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

    export override fn componentCount(self) -> UWord = 1

    export override fn firstComponent(capture self) -> const NamedType = self
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

    export override fn componentCount(self) -> UWord = self.components.size

    export override fn firstComponent(capture self) -> const NamedType = self.components[0]
}

export class TypeArgument : const Any {
    // one of VARIANCE_INVARIANT, VARIANCE_IN, VARIANCE_OUT
    export variance: U8 = init
    export type: const Type = init
}

// TODO: make this a proper enum / union type ones these are implemented
export VARIANCE_INVARIANT: U8 = 0
export VARIANCE_IN: U8 = 1
export VARIANCE_OUT: U8 = 2

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
