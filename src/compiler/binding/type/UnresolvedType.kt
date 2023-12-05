package compiler.binding.type

import compiler.ast.type.TypeModifier
import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.reportings.Reporting

class UnresolvedType private constructor(
    val standInType: ResolvedTypeReference,
    private val reference: TypeReference,
    val parameters: List<ResolvedTypeReference>,
) : ResolvedTypeReference by standInType {
    constructor(context: CTContext, reference: TypeReference, parameters: List<ResolvedTypeReference>) : this(
        getReplacementType(context),
        reference,
        parameters,
    )

    override val simpleName = "<ERROR>"

    override fun validate(): Collection<Reporting> {
        return parameters.flatMap { it.validate() } + setOf(Reporting.unknownType(reference))
    }

    companion object {
        fun getReplacementType(context: CTContext): ResolvedTypeReference {
            return Any.baseReference(context).modifiedWith(TypeModifier.READONLY)
        }
    }
}