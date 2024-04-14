package compiler.binding.basetype

import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.type.BaseType
import compiler.reportings.MultipleInheritanceIssueReporting
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

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

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return clauses.flatMap { it.semanticAnalysisPhase2() }
    }

    /**
     * initialized during [semanticAnalysisPhase3]
     */
    lateinit var inheritedMemberFunctions: List<BoundOverloadSet<BoundMemberFunction>>
        private set

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()

        clauses.flatMap { it.semanticAnalysisPhase3() }.forEach(reportings::add)

        clauses
            .filter { it.resolvedReference != null }
            .groupBy { it.resolvedReference!!.baseType }
            .values
            .filter { it.size > 1}
            .forEach { duplicateSupertypes ->
                duplicateSupertypes
                    .drop(1)
                    .forEach {
                        it as SourceBoundSupertypeDeclaration // TODO this assumption will always be true once all basetypes are declared in emerge source
                        reportings.add(Reporting.duplicateSupertype(it.astNode))
                    }
            }

        val inheritedOverloadSetsByNameAndParameterCount = clauses
            .asSequence()
            .mapNotNull { it.resolvedReference }
            .flatMap { it.memberFunctions }
            .filter { it.declaresReceiver } // static methods are not inherited
            .groupBy { Pair(it.canonicalName.simpleName, it.parameterCount) }

        // TODO: on all inherited member functions, narrow the type of the receiver to the subtype
        // this is currently not easy because the BuiltinTypes are not declared in emerge source, should
        // become very feasible afterwards.
        val localInheritedMemberFunctions = mutableListOf<BoundOverloadSet<BoundMemberFunction>>()
        for ((nameAndParamCount, overloadSets) in inheritedOverloadSetsByNameAndParameterCount) {
            if (overloadSets.size == 1) {
                // any errors relate to the definition of the supertype - not relevant for the subtype
                localInheritedMemberFunctions.add(overloadSets.single())
            } else {
                // ambiguous overloads may result from the diamond problem
                val allOverloads = overloadSets
                    .flatMap { it.overloads }
                val diamondSources = allOverloads
                    .map { (it as BoundDeclaredBaseTypeMemberFunction).declaredOnType } // TODO: this assumption will break sooner or later!
                    .toSet()

                val combinedSetName = CanonicalElementName.Function(
                    typeDef.canonicalName,
                    nameAndParamCount.first
                )
                val combinedSet = BoundOverloadSet(combinedSetName, nameAndParamCount.second, allOverloads)
                val combinedReportings = (combinedSet.semanticAnalysisPhase1() + combinedSet.semanticAnalysisPhase2() + combinedSet.semanticAnalysisPhase3())
                combinedReportings
                    .map { MultipleInheritanceIssueReporting(it, diamondSources, typeDef) }
                    .forEach(reportings::add)
                localInheritedMemberFunctions.add(combinedSet)
            }
        }

        this.inheritedMemberFunctions = localInheritedMemberFunctions
        return reportings
    }
}