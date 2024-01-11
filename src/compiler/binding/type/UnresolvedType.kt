package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
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
    override val sourceLocation = reference.declaringNameToken?.sourceLocation
    override val inherentTypeBindings = TypeUnification.EMPTY

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        return parameters.flatMap { it.validate(TypeUseSite.Irrelevant) } + setOf(Reporting.unknownType(reference))
    }

    override fun withMutability(modifier: TypeMutability?): ResolvedTypeReference {
        return UnresolvedType(
            standInType.withMutability(modifier),
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

    override fun withTypeVariables(variables: List<BoundTypeParameter>): ResolvedTypeReference {
        return UnresolvedType(standInType.withTypeVariables(variables), reference, parameters.map { it.withTypeVariables(variables) })
    }

    override fun unify(assigneeType: ResolvedTypeReference, assignmentLocation: SourceLocation, carry: TypeUnification): TypeUnification {
        return when(assigneeType) {
            is RootResolvedTypeReference,
            is GenericTypeReference,
            is BoundTypeArgument -> standInType.unify(assigneeType, assignmentLocation, carry)
            is UnresolvedType -> standInType.unify(assigneeType.standInType, assignmentLocation, carry)
            is TypeVariable -> assigneeType.flippedUnify(this.standInType, assignmentLocation, carry)
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

    override fun instantiateVariables(context: TypeUnification): ResolvedTypeReference {
        return UnresolvedType(
            standInType.instantiateVariables(context),
            reference,
            emptyList(),
        )
    }

    override fun contextualize(context: TypeUnification): ResolvedTypeReference {
        return UnresolvedType(
            standInType.contextualize(context),
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
            return BuiltinAny.baseReference(context).withMutability(TypeMutability.READONLY)
        }
    }
}