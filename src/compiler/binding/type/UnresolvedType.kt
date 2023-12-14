package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.ast.type.TypeVariance
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

class UnresolvedType private constructor(
    val standInType: ResolvedTypeReference,
    private val reference: TypeReference,
    val parameters: List<BoundTypeArgument>,
) : ResolvedTypeReference {
    constructor(context: CTContext, reference: TypeReference, parameters: List<BoundTypeArgument>) : this(
        getReplacementType(context),
        reference,
        parameters,
    )

    override val simpleName = "<ERROR>"
    override val context get() = standInType.context
    override val isNullable get() = standInType.isNullable
    override val mutability get() = standInType.mutability

    override fun validate(): Collection<Reporting> {
        return parameters.flatMap { it.validate() } + setOf(Reporting.unknownType(reference))
    }

    override fun modifiedWith(modifier: TypeMutability): ResolvedTypeReference {
        return UnresolvedType(
            standInType.modifiedWith(modifier),
            reference,
            parameters.map { it.defaultMutabilityTo(modifier) },
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
        return UnresolvedType(
            standInType.withCombinedMutability(mutability),
            reference,
            parameters.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): ResolvedTypeReference {
        return UnresolvedType(
            standInType.withCombinedNullability(nullability),
            reference,
            parameters,
        )
    }

    override fun evaluateAssignabilityTo(
        other: ResolvedTypeReference,
        assignmentLocation: SourceLocation
    ): ValueNotAssignableReporting? {
        return standInType.evaluateAssignabilityTo(other, assignmentLocation)
    }

    override fun assignMatchQuality(other: ResolvedTypeReference): Int? {
        return standInType.assignMatchQuality(other)
    }

    override fun unify(other: ResolvedTypeReference, carry: TypeUnification): TypeUnification {
        return when(other) {
            is RootResolvedTypeReference -> standInType.unify(other, carry)
            is UnresolvedType -> standInType.unify(other.standInType, carry)
            is GenericTypeReference -> carry.plusRight(other.simpleName, BoundTypeArgument(other.context, null, TypeVariance.UNSPECIFIED, other))
            is BoundTypeArgument -> standInType.unify(other, carry)
        }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): ResolvedTypeReference {
        return UnresolvedType(
            standInType.defaultMutabilityTo(mutability),
            reference,
            parameters.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        return UnresolvedType(
            standInType.closestCommonSupertypeWith(other),
            reference,
            emptyList(),
        )
    }

    override fun hasSameBaseTypeAs(other: ResolvedTypeReference): Boolean {
        return standInType.hasSameBaseTypeAs(other)
    }

    override fun toString() = simpleName

    companion object {
        fun getReplacementType(context: CTContext): ResolvedTypeReference {
            return Any.baseReference(context).modifiedWith(TypeMutability.READONLY)
        }

        fun getTypeParameterDefaultBound(context: CTContext): ResolvedTypeReference {
            return Any.baseReference(context).modifiedWith(TypeMutability.READONLY).withCombinedNullability(TypeReference.Nullability.NULLABLE)
        }
    }
}