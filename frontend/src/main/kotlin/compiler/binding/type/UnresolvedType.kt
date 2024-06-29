package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.SideEffectPrediction
import compiler.binding.context.CTContext
import compiler.lexer.Span
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class UnresolvedType private constructor(
    val standInType: BoundTypeReference,
    private val reference: NamedTypeReference,
    val parameters: List<BoundTypeArgument>?,
) : BoundTypeReference {
    constructor(context: CTContext, reference: NamedTypeReference, parameters: List<BoundTypeArgument>?) : this(
        context.swCtx.unresolvableReplacementType,
        reference,
        parameters,
    )

    override val isNullable get() = standInType.isNullable
    override val mutability get() = standInType.mutability
    override val span = reference.declaringNameToken?.span
    override val inherentTypeBindings = TypeUnification.EMPTY
    override val destructorThrowBehavior = SideEffectPrediction.NEVER // avoid complaining extra

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        return (parameters ?: emptyList()).flatMap { it.validate(forUsage.deriveIrrelevant()) } + setOf(Reporting.unknownType(reference))
    }

    override fun withMutability(modifier: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            standInType.withMutability(modifier),
            reference,
            parameters?.map { it.defaultMutabilityTo(modifier) },
        )
    }

    override fun withCombinedMutability(mutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            standInType.withCombinedMutability(mutability),
            reference,
            parameters?.map { it.defaultMutabilityTo(mutability) },
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
        return UnresolvedType(
            standInType.withTypeVariables(variables),
            reference,
            parameters?.map { it.withTypeVariables(variables) }
        )
    }

    override fun unify(assigneeType: BoundTypeReference, assignmentLocation: Span, carry: TypeUnification): TypeUnification {
        return when(assigneeType) {
            is RootResolvedTypeReference,
            is GenericTypeReference,
            is BoundFunctionType,
            is BoundTypeArgument -> standInType.unify(assigneeType, assignmentLocation, carry)
            is UnresolvedType -> standInType.unify(assigneeType.standInType, assignmentLocation, carry)
            is TypeVariable -> assigneeType.flippedUnify(this.standInType, assignmentLocation, carry)
            is NullableTypeReference -> standInType.unify(assigneeType, assignmentLocation, carry)
        }
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            standInType.defaultMutabilityTo(mutability),
            reference,
            parameters?.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return UnresolvedType(
            standInType.closestCommonSupertypeWith(other),
            reference,
            emptyList(),
        )
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return UnresolvedType(
            standInType.instantiateFreeVariables(context),
            reference,
            emptyList(),
        )
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return UnresolvedType(
            standInType.instantiateAllParameters(context),
            reference,
            emptyList(),
        )
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return standInType.hasSameBaseTypeAs(other)
    }

    override fun toString() = DESCRIPTION

    override fun toBackendIr(): IrType {
        throw InternalCompilerError("Attempting to create backend IR from unresolved type at $span")
    }

    companion object {
        const val DESCRIPTION = "<UNRESOLVED>"
    }
}