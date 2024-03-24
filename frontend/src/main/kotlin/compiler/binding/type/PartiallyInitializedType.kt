package compiler.binding.type

import compiler.InternalCompilerError
import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeReference
import compiler.binding.classdef.BoundClassMemberVariable
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.ir.IrType

/**
 * Used to track partial initialization of objects in constructors and member variable initializers. Cannot be
 * mentioned by source code.
 */
data class PartiallyInitializedType(
    val base: RootResolvedTypeReference,
    val uninitializedMemberVariables: Set<BoundClassMemberVariable>,
) : BoundTypeReference {
    override val isNullable = base.isNullable
    override val simpleName get() = base.simpleName
    override val mutability get() = base.mutability
    override val sourceLocation get() = base.sourceLocation

    override fun defaultMutabilityTo(mutability: TypeMutability?): BoundTypeReference {
        return copy(base = base.defaultMutabilityTo(mutability))
    }

    override fun withMutability(modifier: TypeMutability?): BoundTypeReference {
        return copy(base = base.withMutability(modifier))
    }

    override fun withCombinedMutability(mutability: TypeMutability?): BoundTypeReference {
        return copy(base = base.withCombinedMutability(mutability))
    }

    override fun withCombinedNullability(nullability: TypeReference.Nullability): BoundTypeReference {
        return copy(base = base.withCombinedNullability(nullability))
    }

    override fun validate(forUsage: TypeUseSite): Collection<Reporting> {
        return base.validate(forUsage) + setOf(Reporting.objectNotFullyInitialized(this, forUsage.usageLocation))
    }

    override fun closestCommonSupertypeWith(other: BoundTypeReference): BoundTypeReference {
        throw InternalCompilerError("not implemented as it was assumed that this can never happen")
    }

    override fun withTypeVariables(variables: List<BoundTypeParameter>): BoundTypeReference {
        return copy(base = base.withTypeVariables(variables))
    }

    override fun unify(
        assigneeType: BoundTypeReference,
        assignmentLocation: SourceLocation,
        carry: TypeUnification
    ): TypeUnification {
        throw InternalCompilerError("It should never be possible to assign to a partially initialized type")
    }

    override fun instantiateAllParameters(context: TypeUnification): BoundTypeReference {
        return copy(base = base.instantiateAllParameters(context))
    }

    override fun hasSameBaseTypeAs(other: BoundTypeReference): Boolean {
        return base.hasSameBaseTypeAs(other)
    }

    override val inherentTypeBindings = base.inherentTypeBindings

    override fun toString() = "partially-initialized $base"

    override fun toBackendIr(): IrType = base.toBackendIr()
}