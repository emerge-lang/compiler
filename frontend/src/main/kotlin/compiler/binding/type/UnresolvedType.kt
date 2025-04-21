package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.unknownType
import compiler.lexer.Span
import io.github.tmarsteel.emerge.backend.api.ir.IrType

class UnresolvedType private constructor(
    val standInType: BoundTypeReference,
    private val reference: TypeReference,
    val parameters: List<BoundTypeArgument>?,
) : BoundTypeReference {
    constructor(context: CTContext, reference: TypeReference, parameters: List<BoundTypeArgument>?) : this(
        context.swCtx.unresolvableReplacementType,
        reference,
        parameters,
    )

    override val simpleName = "<ERROR>"
    override val isNullable get() = standInType.isNullable
    override val mutability get() = standInType.mutability
    override val span = reference.declaringNameToken?.span
    override val inherentTypeBindings = TypeUnification.EMPTY

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        diagnosis.unknownType(reference)

        parameters?.forEach { it.validate(forUsage.deriveIrrelevant(), diagnosis) }
    }

    override fun withMutability(mutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            standInType.withMutability(mutability),
            reference,
            parameters?.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun withMutabilityIntersectedWith(mutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            standInType.withMutabilityIntersectedWith(mutability),
            reference,
            parameters?.map { it.defaultMutabilityTo(mutability) },
        )
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference {
        return UnresolvedType(
            standInType.withMutabilityLimitedTo(limitToMutability),
            reference,
            parameters?.map { it.withMutabilityLimitedTo(limitToMutability) },
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

    override fun toString() = simpleName

    override fun toBackendIr(): IrType {
        throw InternalCompilerError("Attempting to create backend IR from unresolved type at $span")
    }
}