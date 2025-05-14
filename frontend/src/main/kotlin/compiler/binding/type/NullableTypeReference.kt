package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.basetype.BoundBaseTypeMemberVariable
import compiler.diagnostic.Diagnosis
import compiler.lexer.Span

class NullableTypeReference private constructor(
    internal val nested: BoundTypeReference
): BoundTypeReference {
    override val context = nested.context
    override val simpleName get() = nested.simpleName
    override val mutability get() = nested.mutability
    override val baseTypeOfLowerBound get() = nested.baseTypeOfLowerBound
    override val span get() = nested.span
    override val isNullable = true
    override val isNothing = false

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeReference {
        return rewrap(nested.defaultMutabilityTo(mutability))
    }

    override fun withMutability(mutability: TypeMutability?): BoundTypeReference {
        return rewrap(nested.withMutability(mutability))
    }

    override fun withMutabilityIntersectedWith(mutability: TypeMutability?): BoundTypeReference {
        return rewrap(nested.withMutabilityIntersectedWith(mutability))
    }

    override fun withMutabilityLimitedTo(limitToMutability: TypeMutability?): BoundTypeReference {
        return rewrap(nested.withMutabilityLimitedTo(limitToMutability))
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return when (nullability) {
            TypeReference.Nullability.NULLABLE -> this
            TypeReference.Nullability.UNSPECIFIED -> this
            TypeReference.Nullability.NOT_NULLABLE -> nested
        }
    }

    override fun validate(forUsage: TypeUseSite, diagnosis: Diagnosis) {
        nested.validate(forUsage, diagnosis)
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        return rewrap(nested.closestCommonSupertypeWith(other))
    }

    override fun findMemberVariable(name: String): Set<BoundBaseTypeMemberVariable> {
        return nested.findMemberVariable(name)
    }

    override fun findMemberFunction(name: String): Collection<BoundOverloadSet<BoundMemberFunction>> {
        return nested.findMemberFunction(name)
    }

    override fun withTypeVariables(variables: Collection<BoundTypeParameter>): BoundTypeReference {
        return rewrap(nested.withTypeVariables(variables))
    }

    override fun unify(
        assigneeType: BoundTypeReference,
        assignmentLocation: Span,
        carry: TypeUnification,
    ): TypeUnification {
        return when(assigneeType) {
            is NullableTypeReference -> nested.unify(assigneeType.nested, assignmentLocation, carry)
            is BoundTypeArgument -> unify(assigneeType.type, assignmentLocation, carry)
            is GenericTypeReference -> if (nested is GenericTypeReference || nested is BoundTypeArgument) {
                nested.unify(assigneeType, assignmentLocation, carry)
            } else {
                unify(assigneeType.effectiveBound, assignmentLocation, carry)
            }
            is TypeVariable -> assigneeType.flippedUnify(this, assignmentLocation, carry)
            else -> nested.unify(assigneeType, assignmentLocation, carry)
        }
    }

    override fun instantiateFreeVariables(context: TypeUnification): BoundTypeReference {
        return rewrap(nested.instantiateFreeVariables(context))
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return rewrap(nested.instantiateAllParameters(context))
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return nested.hasSameBaseTypeAs(other)
    }

    override fun isDisjointWith(other: BoundTypeReference): Boolean {
        return nested.isDisjointWith(other)
    }

    override val inherentTypeBindings get() = nested.inherentTypeBindings

    override fun asAstReference(): TypeReference {
        return nested.asAstReference().withNullability(TypeReference.Nullability.NULLABLE)
    }

    override fun toBackendIr() = nested.toBackendIr().asNullable()

    override fun toString(): String = when (nested) {
        is BoundIntersectionTypeReference -> nested.toString(nullableComponents = true)
        else -> "$nested?"
    }

    private fun rewrap(newNested: BoundTypeReference): BoundTypeReference {
        if (newNested === nested) {
            return this
        }

        if (newNested is NullableTypeReference) {
            return newNested
        }

        return NullableTypeReference(newNested.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE))
    }

    companion object {
        operator fun invoke(nested: BoundTypeReference): BoundTypeReference {
            return when (nested) {
                is NullableTypeReference -> nested
                else -> NullableTypeReference(nested.withCombinedNullability(TypeReference.Nullability.NOT_NULLABLE))
            }
        }
    }
}