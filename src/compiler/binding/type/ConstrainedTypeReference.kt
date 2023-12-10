package compiler.binding.type

import compiler.ast.type.TypeMutability
import compiler.binding.ObjectMember
import compiler.binding.context.CTContext
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import compiler.reportings.ValueNotAssignableReporting

class ConstrainedTypeReference(
    override val context: CTContext,
    val bound: ResolvedTypeReference?,
) : ResolvedTypeReference {
    override val isNullable: Boolean
        get() = TODO("Not yet implemented")

    override val simpleName: String? = null

    override val mutability: TypeMutability
        get() = TODO("Not yet implemented")

    override fun modifiedWith(modifier: TypeMutability): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun withCombinedMutability(mutability: TypeMutability?): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun validate(): Collection<Reporting> {
        TODO("Not yet implemented")
    }

    override fun evaluateAssignabilityTo(
        other: ResolvedTypeReference,
        assignmentLocation: SourceLocation
    ): ValueNotAssignableReporting? {
        TODO("Not yet implemented")
    }

    override fun assignMatchQuality(other: ResolvedTypeReference): Int? {
        TODO("Not yet implemented")
    }

    override fun defaultMutabilityTo(mutability: TypeMutability?): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun closestCommonSupertypeWith(other: ResolvedTypeReference): ResolvedTypeReference {
        TODO("Not yet implemented")
    }

    override fun findMemberVariable(name: String): ObjectMember? {
        TODO("Not yet implemented")
    }
}