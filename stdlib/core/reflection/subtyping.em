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

    if subtype is IntersectionType {
        // TODO: an intersection of two classes has no values and is below every type, the compiler knows that
        // (BoundIntersectionTypeReference.isEffectivelyBottom). The typeinfo doesn't say what is a class.
        components = subtype.asIntersectionType().components
        var index: UWord = 0
        while index < components.size {
            if isSubtypeAtDepth(components.getOrPanic(index), supertype, depth) {
                return true
            }
            set index = index.plusModulo(1 as UWord)
        }
        return false
    }

    return isNamedSubtype(subtype.asNamedType(), supertype.asNamedType(), depth)
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

    if supertype.arguments.size == 0 {
        return true
    }

    translated = subtype.asSupertypeWithBase(supertype.baseType)
    var index: UWord = 0
    while index < supertype.arguments.size {
        if not argumentAccepts(supertype.arguments.getOrPanic(index), translated.arguments.getOrPanic(index), depth.plusModulo(1 as UWord)) {
            return false
        }
        set index = index.plusModulo(1 as UWord)
    }

    return true
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

    components = type.asIntersectionType().components
    var mutability = MUTABILITY_READ
    var index: UWord = 0
    while index < components.size {
        set mutability = intersectMutability(mutability, components.getOrPanic(index).mutability)
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

    if template is NamedType {
        return instantiateNamed(template.asNamedType(), arguments)
    }

    // an intersection that mentions no type parameter
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
