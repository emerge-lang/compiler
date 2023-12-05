package compiler.binding.type

import compiler.ast.type.TypeReference
import compiler.binding.context.CTContext
import compiler.reportings.Reporting

class UnresolvedType(
    context: CTContext,
    private val reference: TypeReference,
    val parameters: List<ResolvedTypeReference>,
) : ResolvedTypeReference by Any.baseReference(context) {
    override val simpleName = "<ERROR>"

    override fun validate(): Collection<Reporting> {
        return parameters.flatMap { it.validate() } + setOf(Reporting.unknownType(reference))
    }
}