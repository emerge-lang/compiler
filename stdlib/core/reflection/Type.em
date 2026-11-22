package emerge.core.reflection

import emerge.platform.panic
import emerge.core.safemath.plusModulo

// runtime type information on a type (as opposed to ReflectionBaseType, which describes a base type only):
// a base type together with nullability, mutability and type arguments, an intersection of those, or a union of
// named types and intersections.
//
// Mutability belongs to a reference, not to the object it refers to: an object doesn't know the mutability of
// the references to it, and the same object is `mut` through one reference and `read` through another. So the
// type of an object (`someObject.type`) says nothing about mutability, it always is `read`. Its type arguments
// are different: an array created as an `Array<mut Foo>` holds `mut` references for as long as it lives.
export interface Type {
    // the same type, with the nullability replaced
    export nothrow fn withNullability(capture self, nullable: Bool) -> const Type

    // the number of named types this type is composed of: 1 for a NamedType, the number of components for an
    // IntersectionType, the sum over the components for a UnionType
    export nothrow fn componentCount(self) -> UWord

    // the first of the named types this type is composed of
    export nothrow fn firstComponent(capture self) -> const NamedType

    export nothrow fn toString(self) -> String
}

export class NamedType : const Type {
    export baseType: ReflectionBaseType = init
    export nullable: Bool = init
    // one of MUTABILITY_READ, MUTABILITY_MUT, MUTABILITY_CONST, MUTABILITY_OWN
    export mutability: U8 = init
    export arguments: const Array<TypeArgument> = init

    export override nothrow fn withNullability(capture self, nullable: Bool) -> const NamedType {
        if self.nullable == nullable {
            return self
        }
        return NamedType(self.baseType, nullable, self.mutability, self.arguments)
    }

    // the same type, with the mutability replaced
    export nothrow fn withMutability(capture self, mutability: U8) -> const NamedType {
        if self.mutability == mutability {
            return self
        }
        return NamedType(self.baseType, self.nullable, mutability, self.arguments)
    }

    export override nothrow fn componentCount(self) -> UWord = 1

    export override nothrow fn firstComponent(capture self) -> const NamedType = self

    export override nothrow fn toString(self) -> String {
        bt = self.baseType
        var str = bt.canonicalName
        if self.mutability == MUTABILITY_MUT {
            set str = "mut " + str
        }
        if self.mutability == MUTABILITY_CONST and not bt.isConst {
            set str = "const " + str
        }
        if self.mutability == MUTABILITY_OWN {
            set str = "own " + str
        }

        if self.arguments.size > 0 {
            set str = str + "<" + self.arguments.getOrPanic(0).toString()
            var index: UWord = 1
            while index < self.arguments.size {
                set str = str + ", " + self.arguments.getOrPanic(index).toString()
                set index = index.plusModulo(1 as UWord)
            }
            set str = str + ">"
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

    export override nothrow fn toString(self) -> String {
        var str = self.components.getOrPanic(0).toString()
        var index: UWord = 1
        while index < self.components.size {
            set str = str + " & " + self.components.getOrPanic(index).toString()
            set index = index.plusModulo(1 as UWord)
        }

        return str
    }
}

// `A | B`: a value of it is a value of one of the components. `BoundUnionTypeReference` in the compiler.
export class UnionType : const Type {
    // at least two, each a NamedType or an IntersectionType, never a UnionType; nullable iff the union is
    export components: const Array<const Type> = init

    export override nothrow fn withNullability(capture self, nullable: Bool) -> const Type {
        newComponents: own Array<const Type> = Array.new::<const Type>(self.components.size, self.components.getOrPanic(0))
        var index: UWord = 0
        while index < self.components.size {
            newComponents.setOrPanic(index, self.components.getOrPanic(index).withNullability(nullable))
            set index = index.plusModulo(1 as UWord)
        }
        return UnionType(newComponents)
    }

    export override nothrow fn componentCount(self) -> UWord {
        var count: UWord = 0
        var index: UWord = 0
        while index < self.components.size {
            set count = count.plusModulo(self.components.getOrPanic(index).componentCount())
            set index = index.plusModulo(1 as UWord)
        }
        return count
    }

    export override nothrow fn firstComponent(capture self) -> const NamedType = self.components.getOrPanic(0).firstComponent()

    export override nothrow fn toString(self) -> String {
        var str = unionComponentToString(self.components.getOrPanic(0))
        var index: UWord = 1
        while index < self.components.size {
            set str = str + " | " + unionComponentToString(self.components.getOrPanic(index))
            set index = index.plusModulo(1 as UWord)
        }

        return str
    }
}

// an intersection binds tighter than a union, the parentheses are for the reader
nothrow fn unionComponentToString(component: const Type) -> String {
    if component is IntersectionType {
        return "(" + component.toString() + ")"
    }
    return component.toString()
}

// stands for a type parameter of a base type in the templates of its supertypes, see
// ReflectionBaseType.supertypeTemplates. Never is the type of a value, and never leaves this package.
class TypeParameterPlaceholder : const Type {
    // the index of the type parameter in the type parameters of the base type
    index: UWord = init
    // one of PLACEHOLDER_NULLABILITY_OF_ARGUMENT (`T`), PLACEHOLDER_NULLABLE (`T?`), PLACEHOLDER_NOT_NULLABLE (`T!`)
    nullability: U8 = init
    // PLACEHOLDER_MUTABILITY_OF_ARGUMENT (`T`), or the mutability written on the type parameter (`mut T`)
    givenMutability: U8 = init

    override nothrow fn withNullability(capture self, nullable: Bool) -> const Type {
        panic("a type parameter placeholder is not a type")
    }

    override nothrow fn componentCount(self) -> UWord = 1

    override nothrow fn firstComponent(capture self) -> const NamedType {
        panic("a type parameter placeholder is not a type")
    }

    override nothrow fn toString(self) -> String = "<type parameter>"

    // @return the type that stands in the place of this placeholder when [argument] is the type argument
    nothrow fn applyNullabilityTo(self, capture argument: const Type) -> const Type {
        var result: const Type = argument
        if self.nullability != PLACEHOLDER_NULLABILITY_OF_ARGUMENT {
            set result = result.withNullability(self.nullability == PLACEHOLDER_NULLABLE)
        }
        if self.givenMutability != PLACEHOLDER_MUTABILITY_OF_ARGUMENT {
            set result = result.withGivenMutability(self.givenMutability)
        }

        return result
    }
}

PLACEHOLDER_NULLABILITY_OF_ARGUMENT: U8 = 0
PLACEHOLDER_NULLABLE: U8 = 1
PLACEHOLDER_NOT_NULLABLE: U8 = 2
PLACEHOLDER_MUTABILITY_OF_ARGUMENT: U8 = 255

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

    override nothrow fn toString(self) -> String = "<intersection template>"
}

// a union in the template of a supertype, with at least one component that mentions a type parameter of the base
// type; see IntersectionTemplate
class UnionTemplate : const Type {
    components: const Array<const Type> = init

    override nothrow fn withNullability(capture self, nullable: Bool) -> const Type {
        panic("a union template is not a type")
    }

    override nothrow fn componentCount(self) -> UWord = self.components.size

    override nothrow fn firstComponent(capture self) -> const NamedType {
        panic("a union template is not a type")
    }

    override nothrow fn toString(self) -> String = "<union template>"
}

export class TypeArgument : const Any {
    // one of VARIANCE_INVARIANT, VARIANCE_IN, VARIANCE_OUT
    export variance: U8 = init
    export value: const Type = init

    export nothrow fn toString(self) -> String {
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

export MUTABILITY_READ: U8 = 0
export MUTABILITY_MUT: U8 = 1
export MUTABILITY_CONST: U8 = 2
export MUTABILITY_OWN: U8 = 3

// @return the mutability that asks for all that both [a] and [b] ask for: `mut` and `const` together are `own`
export nothrow fn intersectMutability(a: U8, b: U8) -> U8 {
    if a == b {
        return a
    }
    if a == MUTABILITY_OWN or b == MUTABILITY_OWN {
        return MUTABILITY_OWN
    }
    if a == MUTABILITY_READ {
        return b
    }
    if b == MUTABILITY_READ {
        return a
    }

    return MUTABILITY_OWN
}

// @return the mutability that both [a] and [b] fit: `mut` and `const` together are `read`. The mutability of a
// union of an `a` and a `b` reference.
export nothrow fn unionMutability(a: U8, b: U8) -> U8 {
    if a == b {
        return a
    }
    if a == MUTABILITY_OWN {
        return b
    }
    if b == MUTABILITY_OWN {
        return a
    }

    return MUTABILITY_READ
}

// what `mut T` is, with [self] for `T` and [given] the mutability written: [self], of the mutability that both
// it and [given] ask for.
//
// What is const is no token, and neither is a `mut T` of a T that cannot be one. `const T` of a `mut X` is an
// `own X`, which doesn't say so anymore; so the result is intersected with NonToken then. This is what
// `GenericTypeReference.instantiateAllParameters` does in the compiler.
export nothrow fn withGivenMutability(capture self: const Type, given: U8) -> const Type {
    isNoToken = given == MUTABILITY_CONST or not self.mayBeToken()
    combined = self.withMutabilityOfAll(intersectMutability(mutabilityOfReference(self), given))
    if isNoToken {
        return combined.asNoToken()
    }

    return combined
}

// @return [self], with the mutability of all of its components replaced
nothrow fn withMutabilityOfAll(capture self: const Type, mutability: U8) -> const Type {
    if self is NamedType {
        return self.asNamedType().withMutability(mutability)
    }

    if self is UnionType {
        unionComponents = self.asUnionType().components
        newUnionComponents: own Array<const Type> = Array.new::<const Type>(unionComponents.size, unionComponents.getOrPanic(0))
        var unionIndex: UWord = 0
        while unionIndex < unionComponents.size {
            newUnionComponents.setOrPanic(unionIndex, unionComponents.getOrPanic(unionIndex).withMutabilityOfAll(mutability))
            set unionIndex = unionIndex.plusModulo(1 as UWord)
        }
        return UnionType(newUnionComponents)
    }

    components = self.asIntersectionType().components
    newComponents: own Array<NamedType> = Array.new::<NamedType>(components.size, components.getOrPanic(0))
    var index: UWord = 0
    while index < components.size {
        newComponents.setOrPanic(index, components.getOrPanic(index).withMutability(mutability))
        set index = index.plusModulo(1 as UWord)
    }
    return IntersectionType(newComponents)
}

// the runtime type information for the type argument. Type parameters are reified, so this works for type
// parameters of the enclosing function or class, too: `typeOf::<T>()`
export nothrow intrinsic fn typeOf<T>() -> const Type

// The intersection of the given types; nested intersections are flattened. As in the compiler
// (`BoundIntersectionTypeReference.ofComponents`), the components take the mutability they have in common:
// `mut A & const B` is `own A & own B`. Where a component cannot be a token (that `const B`) and the result
// doesn't say so anymore, it is intersected with NonToken.
export nothrow fn intersectionOf(capture components: const Array<const Type>) -> const Type {
    // a union component distributes: `(A | B) & C` is `(A & C) | (B & C)`, so an intersection never holds a union
    // (`BoundIntersectionTypeReference.ofComponents` in the compiler)
    var unionIndex: UWord = 0
    while unionIndex < components.size {
        if components.getOrPanic(unionIndex) is UnionType {
            alternatives = components.getOrPanic(unionIndex).asUnionType().components
            distributed: own Array<const Type> = Array.new::<const Type>(alternatives.size, alternatives.getOrPanic(0))
            var alternativeIndex: UWord = 0
            while alternativeIndex < alternatives.size {
                withAlternative: own Array<const Type> = Array.new::<const Type>(components.size, components.getOrPanic(0))
                var copyIndex: UWord = 0
                while copyIndex < components.size {
                    withAlternative.setOrPanic(copyIndex, components.getOrPanic(copyIndex))
                    set copyIndex = copyIndex.plusModulo(1 as UWord)
                }
                withAlternative.setOrPanic(unionIndex, alternatives.getOrPanic(alternativeIndex))
                distributed.setOrPanic(alternativeIndex, intersectionOf(withAlternative))
                set alternativeIndex = alternativeIndex.plusModulo(1 as UWord)
            }
            return unionOf(distributed)
        }
        set unionIndex = unionIndex.plusModulo(1 as UWord)
    }

    var count: UWord = 0
    var mutability = MUTABILITY_READ
    var anyIsNoToken = false
    var index: UWord = 0
    while index < components.size {
        component = components.getOrPanic(index)
        set count = count.plusModulo(component.componentCount())
        set mutability = intersectMutability(mutability, assignmentMutabilityOfAll(component))
        if not component.mayBeToken() {
            set anyIsNoToken = true
        }
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
                flat.setOrPanic(flatIndex, nested.getOrPanic(nestedIndex).withMutability(mutability))
                set flatIndex = flatIndex.plusModulo(1 as UWord)
                set nestedIndex = nestedIndex.plusModulo(1 as UWord)
            }
        } else {
            flat.setOrPanic(flatIndex, component.asNamedType().withMutability(mutability))
            set flatIndex = flatIndex.plusModulo(1 as UWord)
        }
        set index = index.plusModulo(1 as UWord)
    }

    intersection: const Type = IntersectionType(flat)
    if anyIsNoToken {
        return intersection.asNoToken()
    }

    return intersection
}

// The union of the given types; nested unions are flattened. As in the compiler (`BoundUnionTypeReference.ofComponents`),
// the union is nullable where a component is, and so are all of its components then: `A | B?` is `(A | B)?`.
export nothrow fn unionOf(capture components: const Array<const Type>) -> const Type {
    var count: UWord = 0
    var anyNullable = false
    var index: UWord = 0
    while index < components.size {
        component = components.getOrPanic(index)
        if component is UnionType {
            set count = count.plusModulo(component.asUnionType().components.size)
        } else {
            set count = count.plusModulo(1 as UWord)
        }
        if component.isNullable() {
            set anyNullable = true
        }
        set index = index.plusModulo(1 as UWord)
    }

    if count == 1 {
        return components.getOrPanic(0)
    }

    flat: own Array<const Type> = Array.new::<const Type>(count, components.getOrPanic(0))
    var flatIndex: UWord = 0
    set index = 0
    while index < components.size {
        component = components.getOrPanic(index)
        if component is UnionType {
            nested = component.asUnionType().components
            var nestedIndex: UWord = 0
            while nestedIndex < nested.size {
                flat.setOrPanic(flatIndex, nested.getOrPanic(nestedIndex).withNullability(anyNullable))
                set flatIndex = flatIndex.plusModulo(1 as UWord)
                set nestedIndex = nestedIndex.plusModulo(1 as UWord)
            }
        } else {
            flat.setOrPanic(flatIndex, component.withNullability(anyNullable))
            set flatIndex = flatIndex.plusModulo(1 as UWord)
        }
        set index = index.plusModulo(1 as UWord)
    }

    return UnionType(flat)
}

// The casts of this package, for code that is nothrow and knows what it has: `as` throws, so nothrow code cannot use it

nothrow fn asNamedType(capture self: const Type) -> const NamedType {
    return (self as? NamedType) ?: panic("not a NamedType")
}

nothrow fn asIntersectionType(capture self: const Type) -> const IntersectionType {
    return (self as? IntersectionType) ?: panic("not an IntersectionType")
}

nothrow fn asUnionType(capture self: const Type) -> const UnionType {
    return (self as? UnionType) ?: panic("not a UnionType")
}

nothrow fn asUnionTemplate(capture self: const Type) -> const UnionTemplate {
    return (self as? UnionTemplate) ?: panic("not a UnionTemplate")
}

nothrow fn asTypeParameterPlaceholder(capture self: const Type) -> const TypeParameterPlaceholder {
    return (self as? TypeParameterPlaceholder) ?: panic("not a TypeParameterPlaceholder")
}

nothrow fn asIntersectionTemplate(capture self: const Type) -> const IntersectionTemplate {
    return (self as? IntersectionTemplate) ?: panic("not an IntersectionTemplate")
}

export nothrow intrinsic get fn type(self: Any) -> NamedType