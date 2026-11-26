package emerge.core.reflection

import emerge.platform.panic
import emerge.core.safemath.plusModulo

// The subtype relation on runtime types. It has to agree with what the compiler does for types without type
// variables (`BoundTypeReference.unify` in the frontend). The frontend generates the test that compares the
// two (`RuntimeSubtypingGridTests`).
//
// All of it is nothrow, as `is` is.

// how many levels of type arguments isSubtypeOf follows before it gives up and denies the relation. Some
// questions never end otherwise: with `class K : Cn<Cn<in K>>`, deciding `K` below `Cn<in K>` asks for itself
// again. The compiler denies those, too.
MAX_SUBTYPE_CHECK_DEPTH: UWord = 64

// whether every value of [self] is a value of [supertype]
export nothrow fn isSubtypeOf(capture self: const Type, supertype: const Type) -> Bool {
    return isSubtypeAtDepth(self, supertype, 0)
}

nothrow fn isSubtypeAtDepth(subtype: const Type, supertype: const Type, depth: UWord) -> Bool {
    if depth > MAX_SUBTYPE_CHECK_DEPTH {
        return false
    }

    if supertype is IntersectionType {
        components = supertype.asIntersectionType().components
        var index: UWord = 0
        while index < components.size {
            if not isSubtypeAtDepth(subtype, components.getOrPanic(index), depth) {
                return false
            }
            set index = index.plusModulo(1 as UWord)
        }
        return true
    }

    if supertype is UnionType {
        superComponents = supertype.asUnionType().components
        if subtype is UnionType {
            // each alternative of the subtype is a value of the supertype (`Subtyping.union_flipped_unify` in the proofs)
            subComponents = subtype.asUnionType().components
            var subIndex: UWord = 0
            while subIndex < subComponents.size {
                if not isSubtypeAtDepth(subComponents.getOrPanic(subIndex), supertype, depth) {
                    return false
                }
                set subIndex = subIndex.plusModulo(1 as UWord)
            }
            return true
        }

        if subtype is IntersectionType {
            // every value of the intersection is one of each component, so one below the union suffices:
            // `(A | B) & C` is below `A | B`. Where none is, a component of the union may take the whole intersection
            if intersectionIsSubtype(subtype.asIntersectionType(), supertype, depth) {
                return true
            }
        }

        // the first component that takes the value takes it for the union (`Subtyping.union_body` in the proofs)
        var superIndex: UWord = 0
        while superIndex < superComponents.size {
            if isSubtypeAtDepth(subtype, superComponents.getOrPanic(superIndex), depth) {
                return true
            }
            set superIndex = superIndex.plusModulo(1 as UWord)
        }
        return false
    }

    if subtype is UnionType {
        // a value of the union is one of any component, so each has to fit
        components = subtype.asUnionType().components
        var index: UWord = 0
        while index < components.size {
            if not isSubtypeAtDepth(components.getOrPanic(index), supertype, depth) {
                return false
            }
            set index = index.plusModulo(1 as UWord)
        }
        return true
    }

    if subtype is IntersectionType {
        return intersectionIsSubtype(subtype.asIntersectionType(), supertype, depth)
    }

    return isNamedSubtype(subtype.asNamedType(), supertype.asNamedType(), depth)
}

// whether every value of the intersection [subtype] is a value of [supertype], a named type or a union
nothrow fn intersectionIsSubtype(subtype: const IntersectionType, supertype: const Type, depth: UWord) -> Bool {
    components = subtype.components
    if hasDisjointClasses(components) {
        // no object is of two classes, so the intersection has no values but null, if it is nullable: it is
        // Nothing by another name, and below every type that takes its null
        // (`BoundIntersectionTypeReference.isEffectivelyBottom` in the compiler)
        return supertype.isNullable() or not subtype.isNullable()
    }

    // Where the intersection cannot be a token as a whole (`own Animal & NonToken`), the value may freeze,
    // though a component alone (`own Animal`) doesn't say so. So such a component is also tried as the const
    // it can become.
    componentsMayFreeze = not subtype.mayBeToken()
    var index: UWord = 0
    while index < components.size {
        component = components.getOrPanic(index)
        if isSubtypeAtDepth(component, supertype, depth) {
            return true
        }
        if componentsMayFreeze and component.assignmentMutability() == MUTABILITY_OWN and component.mayBeToken() {
            if isSubtypeAtDepth(component.withMutability(MUTABILITY_CONST), supertype, depth) {
                return true
            }
        }
        set index = index.plusModulo(1 as UWord)
    }
    return false
}

// whether two of [components] are of different classes
nothrow fn hasDisjointClasses(components: const Array<NamedType>) -> Bool {
    var first: UWord = 0
    while first < components.size {
        firstBaseType = components.getOrPanic(first).baseType
        if firstBaseType.isClass {
            var second: UWord = first.plusModulo(1 as UWord)
            while second < components.size {
                secondBaseType = components.getOrPanic(second).baseType
                if secondBaseType.isClass and not firstBaseType.isSameAs(secondBaseType) {
                    return true
                }
                set second = second.plusModulo(1 as UWord)
            }
        }
        set first = first.plusModulo(1 as UWord)
    }

    return false
}

nothrow fn isNamedSubtype(subtype: const NamedType, supertype: const NamedType, depth: UWord) -> Bool {
    if subtype.nullable and not supertype.nullable {
        return false
    }

    if not subtype.baseType.isSubtypeOf(supertype.baseType) {
        return false
    }

    if not mutabilityIsAssignable(subtype.assignmentMutability(), supertype.assignmentMutability()) {
        return false
    }

    if subtype.baseType.isSameAs(typeOf::<Nothing>().firstComponent().baseType) {
        return true
    }

    if supertype.arguments.size > 0 {
        translated = subtype.asSupertypeWithBase(supertype.baseType)
        var index: UWord = 0
        while index < supertype.arguments.size {
            if not argumentAccepts(supertype.arguments.getOrPanic(index), translated.arguments.getOrPanic(index), depth.plusModulo(1 as UWord)) {
                return false
            }
            set index = index.plusModulo(1 as UWord)
        }
    }

    // it is a subtype. Still, a token is never frozen, and stays visible in the type of every reference to it:
    // what may be a token is not below a type that cannot be one (`TokenRule` in the compiler)
    if subtype.mayBeToken() and not supertype.mayBeToken() {
        return false
    }

    return true
}

// Whether a value of this type may be a token, or hold one. It cannot where the type is const, as a token is
// never frozen; nor where its base type is no token (ReflectionBaseType.isNonToken) and none of its type
// arguments may be one. One component of an intersection that cannot be a token decides it for the intersection;
// one component of a union that may be one decides it for the union.
// `BoundTypeReference.mayBeToken` in the compiler.
export nothrow fn mayBeToken(capture self: const Type) -> Bool {
    if self is NamedType {
        return namedTypeMayBeToken(self.asNamedType())
    }

    if self is UnionType {
        unionComponents = self.asUnionType().components
        var unionIndex: UWord = 0
        while unionIndex < unionComponents.size {
            if unionComponents.getOrPanic(unionIndex).mayBeToken() {
                return true
            }
            set unionIndex = unionIndex.plusModulo(1 as UWord)
        }
        return false
    }

    components = self.asIntersectionType().components
    var index: UWord = 0
    while index < components.size {
        if not namedTypeMayBeToken(components.getOrPanic(index)) {
            return false
        }
        set index = index.plusModulo(1 as UWord)
    }

    return true
}

nothrow fn namedTypeMayBeToken(type: const NamedType) -> Bool {
    if type.mutability == MUTABILITY_CONST or type.baseType.isConst {
        return false
    }

    if not type.baseType.isNonToken {
        return true
    }

    var index: UWord = 0
    while index < type.arguments.size {
        argument = type.arguments.getOrPanic(index)
        // an `in` argument reads as `Any?`, which may be a token
        if argument.variance == VARIANCE_IN or argument.value.mayBeToken() {
            return true
        }
        set index = index.plusModulo(1 as UWord)
    }

    return false
}

// @return [self], of values that are no tokens: itself if it cannot be one (see mayBeToken), its intersection
// with NonToken otherwise. `BoundTypeReference.asNoToken` in the compiler.
nothrow fn asNoToken(capture self: const Type) -> const Type {
    if not self.mayBeToken() {
        return self
    }

    if self is UnionType {
        // by alternative: `(A | B) & NonToken` is `(A & NonToken) | (B & NonToken)`
        unionComponents = self.asUnionType().components
        newUnionComponents: own Array<const Type> = Array.new::<const Type>(unionComponents.size, unionComponents.getOrPanic(0))
        var unionIndex: UWord = 0
        while unionIndex < unionComponents.size {
            newUnionComponents.setOrPanic(unionIndex, unionComponents.getOrPanic(unionIndex).asNoToken())
            set unionIndex = unionIndex.plusModulo(1 as UWord)
        }
        return unionOf(newUnionComponents)
    }

    mutability = assignmentMutabilityOfAll(self)
    nonToken = typeOf::<NonToken>().firstComponent().withNullability(self.isNullable()).withMutability(mutability)
    count = self.componentCount()
    components: own Array<NamedType> = Array.new::<NamedType>(count.plusModulo(1 as UWord), nonToken)
    if self is IntersectionType {
        ownComponents = self.asIntersectionType().components
        var index: UWord = 0
        while index < count {
            components.setOrPanic(index, ownComponents.getOrPanic(index).withMutability(mutability))
            set index = index.plusModulo(1 as UWord)
        }
    } else {
        components.setOrPanic(0, self.asNamedType().withMutability(mutability))
    }

    return IntersectionType(components)
}

// @return the mutability that the components of [type] have in common when intersected: that which asks for
// all that any of them asks for. Of a union, the mutability that each alternative fits.
nothrow fn assignmentMutabilityOfAll(type: const Type) -> U8 {
    if type is NamedType {
        return type.asNamedType().assignmentMutability()
    }

    if type is UnionType {
        unionComponents = type.asUnionType().components
        var joined = MUTABILITY_OWN
        var unionIndex: UWord = 0
        while unionIndex < unionComponents.size {
            set joined = unionMutability(joined, assignmentMutabilityOfAll(unionComponents.getOrPanic(unionIndex)))
            set unionIndex = unionIndex.plusModulo(1 as UWord)
        }
        return joined
    }

    components = type.asIntersectionType().components
    var mutability = MUTABILITY_READ
    var index: UWord = 0
    while index < components.size {
        set mutability = intersectMutability(mutability, components.getOrPanic(index).assignmentMutability())
        set index = index.plusModulo(1 as UWord)
    }

    return mutability
}

// whether a reference of the mutability [from] can be assigned to one of the mutability [to]
export nothrow fn mutabilityIsAssignable(from: U8, to: U8) -> Bool {
    if from == to or from == MUTABILITY_OWN {
        return true
    }

    if from == MUTABILITY_READ {
        return false
    }

    return to == MUTABILITY_READ
}

// The mutability that matters for assigning: objects of types that are const by themselves have no state
// that could be changed, so references to them are as good as any.
nothrow fn assignmentMutability(self: const NamedType) -> U8 {
    if self.baseType.isConst {
        return MUTABILITY_OWN
    }

    return self.mutability
}

// @return the mutability of a reference of the type [type]
nothrow fn mutabilityOfReference(type: const Type) -> U8 {
    if type is NamedType {
        return type.asNamedType().mutability
    }

    if type is UnionType {
        unionComponents = type.asUnionType().components
        var joined = MUTABILITY_OWN
        var unionIndex: UWord = 0
        while unionIndex < unionComponents.size {
            set joined = unionMutability(joined, mutabilityOfReference(unionComponents.getOrPanic(unionIndex)))
            set unionIndex = unionIndex.plusModulo(1 as UWord)
        }
        return joined
    }

    components = type.asIntersectionType().components
    var mutability = MUTABILITY_READ
    var index: UWord = 0
    while index < components.size {
        component = components.getOrPanic(index)
        if component.baseType.isConst {
            return MUTABILITY_CONST
        }
        set mutability = intersectMutability(mutability, component.mutability)
        set index = index.plusModulo(1 as UWord)
    }

    return mutability
}

// whether a type with [target] for a type argument takes one with [source] in its place
nothrow fn argumentAccepts(target: TypeArgument, source: TypeArgument, depth: UWord) -> Bool {
    if target.variance == VARIANCE_INVARIANT {
        if source.variance != VARIANCE_INVARIANT {
            return false
        }

        // the target uses the type both ways, so the two have to be the same type
        return isSubtypeAtDepth(source.value, target.value, depth) and isSubtypeAtDepth(target.value, source.value, depth)
    }

    if target.variance == VARIANCE_OUT {
        if source.variance == VARIANCE_IN {
            // all that is known of what comes out of the source is that it is a value
            return isSubtypeAtDepth(typeOf::<read Any?>(), target.value, depth)
        }

        return isSubtypeAtDepth(source.value, target.value, depth)
    }

    if source.variance == VARIANCE_OUT {
        // the source takes nothing, so the target must not take anything either
        return isSubtypeAtDepth(target.value, typeOf::<own Nothing>(), depth)
    }

    return isSubtypeAtDepth(target.value, source.value, depth)
}

// @return this type as seen through its supertype [superBaseType]: `Seq<Box<A>>` for a `Nest<A>` of
// `class Nest<E> : Seq<Box<E>>`. [superBaseType] must be a supertype of the base type of this type, and
// have type parameters. The result is not nullable, whatever this type is.
nothrow fn asSupertypeWithBase(capture self: const NamedType, borrow superBaseType: ReflectionBaseType) -> const NamedType {
    if self.baseType.isSameAs(superBaseType) {
        return self
    }

    template = self.baseType.supertypeTemplateFor(superBaseType)
        ?: panic("the runtime type information is inconsistent: missing the type arguments of a supertype")

    return instantiateNamed(template, self.arguments)
}

// @return [template] with the type arguments [arguments] in place of the type parameter placeholders. This is
// what `BoundTypeReference.instantiateAllParameters` does in the compiler.
nothrow fn instantiate(capture template: const Type, arguments: const Array<TypeArgument>) -> const Type {
    if template is TypeParameterPlaceholder {
        placeholder = template.asTypeParameterPlaceholder()
        return placeholder.applyNullabilityTo(arguments.getOrPanic(placeholder.index).value)
    }

    if template is IntersectionTemplate {
        components = template.asIntersectionTemplate().components
        instantiated: own Array<const Type> = Array.new::<const Type>(components.size, components.getOrPanic(0))
        var index: UWord = 0
        while index < components.size {
            instantiated.setOrPanic(index, instantiate(components.getOrPanic(index), arguments))
            set index = index.plusModulo(1 as UWord)
        }
        return intersectionOf(instantiated)
    }

    if template is UnionTemplate {
        unionComponents = template.asUnionTemplate().components
        instantiatedUnion: own Array<const Type> = Array.new::<const Type>(unionComponents.size, unionComponents.getOrPanic(0))
        var unionIndex: UWord = 0
        while unionIndex < unionComponents.size {
            instantiatedUnion.setOrPanic(unionIndex, instantiate(unionComponents.getOrPanic(unionIndex), arguments))
            set unionIndex = unionIndex.plusModulo(1 as UWord)
        }
        return unionOf(instantiatedUnion)
    }

    if template is NamedType {
        return instantiateNamed(template.asNamedType(), arguments)
    }

    // an intersection or union that mentions no type parameter
    return template
}

nothrow fn instantiateNamed(capture template: const NamedType, arguments: const Array<TypeArgument>) -> const NamedType {
    if template.arguments.size == 0 {
        return template
    }

    instantiated: own Array<TypeArgument> = Array.new::<TypeArgument>(template.arguments.size, template.arguments.getOrPanic(0))
    var index: UWord = 0
    while index < template.arguments.size {
        instantiated.setOrPanic(index, instantiateArgument(template.arguments.getOrPanic(index), arguments))
        set index = index.plusModulo(1 as UWord)
    }

    return NamedType(template.baseType, template.nullable, template.mutability, instantiated)
}

// The variance of the result merges that of [template] with that of the type arguments it mentions, like
// `BoundTypeArgument.instantiateWith` does in the compiler.
nothrow fn instantiateArgument(capture template: const TypeArgument, arguments: const Array<TypeArgument>) -> const TypeArgument {
    templateValue = template.value
    if templateValue is TypeParameterPlaceholder {
        placeholder = templateValue.asTypeParameterPlaceholder()
        binding = arguments.getOrPanic(placeholder.index)
        if binding.variance == VARIANCE_INVARIANT or template.variance == VARIANCE_INVARIANT or binding.variance == template.variance {
            variance = if binding.variance == VARIANCE_INVARIANT template.variance else binding.variance
            return TypeArgument(variance, placeholder.applyNullabilityTo(binding.value))
        }

        // the two variances contradict each other
        if template.variance == VARIANCE_OUT {
            return TypeArgument(VARIANCE_OUT, typeOf::<read Any?>())
        }

        return TypeArgument(VARIANCE_IN, typeOf::<own Nothing>())
    }

    if not mentionsVariantArgumentInTypeArguments(templateValue, arguments) {
        return TypeArgument(template.variance, instantiate(templateValue, arguments))
    }

    // `Box<E>` for a type argument, with `out A` for `E`: it may be a `Box<B>` for any subtype B of A
    if template.variance == VARIANCE_IN {
        return TypeArgument(VARIANCE_IN, typeOf::<own Nothing>())
    }

    return TypeArgument(VARIANCE_OUT, instantiate(templateValue, arguments))
}

// whether [template] mentions a type parameter whose type argument in [arguments] has a variance
nothrow fn mentionsVariantArgument(template: const Type, arguments: const Array<TypeArgument>) -> Bool {
    if template is TypeParameterPlaceholder {
        return arguments.getOrPanic(template.asTypeParameterPlaceholder().index).variance != VARIANCE_INVARIANT
    }

    if template is IntersectionTemplate {
        components = template.asIntersectionTemplate().components
        var index: UWord = 0
        while index < components.size {
            if mentionsVariantArgument(components.getOrPanic(index), arguments) {
                return true
            }
            set index = index.plusModulo(1 as UWord)
        }
        return false
    }

    return mentionsVariantArgumentInTypeArguments(template, arguments)
}

// like [mentionsVariantArgument], but a type parameter that is [template] itself, or a component of it, doesn't count
nothrow fn mentionsVariantArgumentInTypeArguments(template: const Type, arguments: const Array<TypeArgument>) -> Bool {
    if template is NamedType {
        templateArguments = template.asNamedType().arguments
        var index: UWord = 0
        while index < templateArguments.size {
            if mentionsVariantArgument(templateArguments.getOrPanic(index).value, arguments) {
                return true
            }
            set index = index.plusModulo(1 as UWord)
        }
        return false
    }

    if template is IntersectionTemplate {
        components = template.asIntersectionTemplate().components
        var index: UWord = 0
        while index < components.size {
            if mentionsVariantArgumentInTypeArguments(components.getOrPanic(index), arguments) {
                return true
            }
            set index = index.plusModulo(1 as UWord)
        }
        return false
    }

    return false
}
