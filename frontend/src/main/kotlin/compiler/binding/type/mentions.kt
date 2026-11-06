package compiler.binding.type

/**
 * Whether this type mentions a [TypeVariable], also in the bounds of the [GenericTypeReference]s in it.
 */
internal fun BoundTypeReference.mentionsTypeVariables(): Boolean = when (this) {
    is TypeVariable -> true
    is GenericTypeReference -> hasTypeVariables
    is RootResolvedTypeReference -> arguments?.any { it.mentionsTypeVariables() } == true
    is NullableTypeReference -> nested.mentionsTypeVariables()
    is BoundTypeArgument -> type.mentionsTypeVariables()
    is BoundIntersectionTypeReference -> components.any { it.mentionsTypeVariables() }
    is ErroneousType -> false
}

/**
 * Whether this type mentions the [TypeVariable] of [parameter].
 */
internal fun BoundTypeReference.mentionsTypeVariable(parameter: BoundTypeParameter): Boolean = when (this) {
    is TypeVariable -> this.parameter == parameter
    is GenericTypeReference -> false
    is RootResolvedTypeReference -> arguments?.any { it.mentionsTypeVariable(parameter) } == true
    is NullableTypeReference -> nested.mentionsTypeVariable(parameter)
    is BoundTypeArgument -> type.mentionsTypeVariable(parameter)
    is BoundIntersectionTypeReference -> components.any { it.mentionsTypeVariable(parameter) }
    is ErroneousType -> false
}

/**
 * Whether this type mentions [parameter], as a [GenericTypeReference].
 */
internal fun BoundTypeReference.mentionsTypeParameter(parameter: BoundTypeParameter): Boolean = when (this) {
    is TypeVariable -> false
    is GenericTypeReference -> this.parameter == parameter
    is RootResolvedTypeReference -> arguments?.any { it.mentionsTypeParameter(parameter) } == true
    is NullableTypeReference -> nested.mentionsTypeParameter(parameter)
    is BoundTypeArgument -> type.mentionsTypeParameter(parameter)
    is BoundIntersectionTypeReference -> components.any { it.mentionsTypeParameter(parameter) }
    is ErroneousType -> false
}
