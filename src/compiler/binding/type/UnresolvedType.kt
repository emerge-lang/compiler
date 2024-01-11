package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting

class UnresolvedType private constructor(
    val standInType: BoundTypeReference,
    private val reference: TypeReference,
    val parameters: List<BoundTypeArgument>,
) : BoundTypeReference {
    constructor(reference: TypeReference, parameters: List<BoundTypeArgument>) : this(
        STAND_IN_TYPE,
        reference,
        parameters,
    )

    override val simpleName = "<ERROR>"
    override val isNullable get() = standInType.isNullable
    override val mutability get() = standInType.mutability
    override val sourceLocation = reference.declaringNameToken?.sourceLocation
    override val inherentTypeBindings = TypeUnification.EMPTY

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        return parameters.flatMap { it.validate(TypeUseSite.Irrelevant) } + setOf(Reporting.unknownType(reference))
    }

    override fun withMutability(modifier: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            standInType.withMutability(modifier),
            reference,
            parameters.map { it.defaultMutabilityTo(modifier) },
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            standInType.withCombinedMutability(mutability),
            reference,
            parameters.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return UnresolvedType(
            standInType.withCombinedNullability(nullability),
            reference,
            parameters,
        )
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): BoundTypeReference {
        return UnresolvedType(standInType.withTypeVariables(variables), reference, parameters.map { it.withTypeVariables(variables) })
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
        return when(assigneeType) {
            is RootResolvedTypeReference,
            is GenericTypeReference,
            is BoundTypeArgument -> standInType.unify(assigneeType, assignmentLocation, carry)
            is UnresolvedType -> standInType.unify(assigneeType.standInType, assignmentLocation, carry)
            is TypeVariable -> assigneeType.flippedUnify(this.standInType, assignmentLocation, carry)
        }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            standInType.defaultMutabilityTo(mutability),
            reference,
            parameters.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return UnresolvedType(
            standInType.closestCommonSupertypeWith(other),
            reference,
            emptyList(),
        )
    }

    override fun instantiateVariables(context: TypeUnification): BoundTypeReference {
        return UnresolvedType(
            standInType.instantiateVariables(context),
            reference,
            emptyList(),
        )
    }

    override fun contextualize(context: TypeUnification): BoundTypeReference {
        return UnresolvedType(
            standInType.contextualize(context),
            reference,
            emptyList(),
        )
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return standInType.hasSameBaseTypeAs(other)
    }

    override fun toString() = simpleName

    companion object {
        val STAND_IN_TYPE: BoundTypeReference = BuiltinAny.baseReference
            .withMutability(TypeMutability.READONLY)
            .withCombinedNullability(TypeReference.Nullability.NULLABLE)
    }
}