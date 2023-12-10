package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.ast.type.TypeVariance
import compiler.binding.ObjectMember
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

class VariantTypeReference(
    val type: ResolvedTypeReference,
    val variance: TypeVariance,
) : ResolvedTypeReference {
    init {
        check(variance != TypeVariance.UNSPECIFIED)
    }

    override val context = type.context
    override val isNullable = type.isNullable
    override val simpleName = type.simpleName
    override val mutability = type.mutability

    override fun modifiedWith(modifier: TypeMutability): ResolvedTypeReference {
        return VariantTypeReference(type.modifiedWith(modifier), variance)
    }

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
        return VariantTypeReference(type.withCombinedMutability(mutability), variance)
    }

    override fun validate(): Collection<Reporting> {
        // TODO: variant(variant(X))?
        return type.validate()
    }

    override fun evaluateAssignabilityTo(
        other: ResolvedTypeReference,
        assignmentLocation: SourceLocation
    ): ValueNotAssignableReporting? {
        // TODO
        return null
    }

    override fun assignMatchQuality(other: ResolvedTypeReference): Int? {
        // is there something TODO here?
        return type.assignMatchQuality(other)
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): ResolvedTypeReference {
        return VariantTypeReference(type.defaultMutabilityTo(mutability), variance)
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        // TODO: how does variance affect this?
        return VariantTypeReference(type.closestCommonSupertypeWith(other), variance)
    }

    override fun findMemberVariable(name: String): ObjectMember? {
        TODO("Not yet implemented")
    }
}