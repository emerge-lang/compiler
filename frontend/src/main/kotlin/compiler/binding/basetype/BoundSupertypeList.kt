package compiler.binding.basetype

import compiler.binding.BoundMemberFunction
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.type.BaseType
import compiler.binding.type.RootResolvedTypeReference
import compiler.reportings.Reporting

class BoundSupertypeList(
    val clauses: List<BoundSupertypeDeclaration>,
    getTypeDef: () -> BaseType,
) : SemanticallyAnalyzable {
    private val typeDef by lazy(getTypeDef)

    /** the base types that are being extended from, initialized in [semanticAnalysisPhase1] */
    lateinit var baseTypes: List<BaseType>
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        clauses.flatMap { it.semanticAnalysisPhase1() }.forEach(reportings::add)
        baseTypes = clauses.mapNotNull { it.resolvedReference?.baseType }
        return reportings
    }

    /**
     * initialized during [semanticAnalysisPhase2]. Will contain duplicates by [BoundMemberFunction.canonicalName]
     * and parameter count. This is because the overload-set level logic on a derived type also needs to account
     * for the additional [BoundMemberFunction]s in that derived type. So the merging of overloads happens in
     * [BoundBaseTypeDefinition].
     */
    lateinit var inheritedMemberFunctions: List<InheritedBoundMemberFunction>
        private set

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        clauses.forEach {
            reportings.addAll(it.semanticAnalysisPhase2())
        }

        val distinctSuperBaseTypes = mutableSetOf<BaseType>()
        val distinctSupertypes = ArrayList<RootResolvedTypeReference>(clauses.size)
        for (clause in clauses) {
            val resolvedReference = clause.resolvedReference ?: continue
            if (!distinctSuperBaseTypes.add(resolvedReference.baseType)) {
                clause as SourceBoundSupertypeDeclaration // TODO this assumption will always be true once all basetypes are declared in emerge source
                reportings.add(Reporting.duplicateSupertype(clause.astNode))
            }

            distinctSupertypes.add(resolvedReference)
        }

        this.inheritedMemberFunctions = distinctSupertypes
            .asSequence()
            .flatMap { it.memberFunctions }
            .filter { it.declaresReceiver }
            .flatMap { it.overloads }
            .map { InheritedBoundMemberFunction(it, typeDef) }
            .toList()

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        clauses.flatMap { it.semanticAnalysisPhase3() }.forEach(reportings::add)

        return reportings
    }
}