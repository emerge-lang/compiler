package compiler.binding.basetype

import compiler.ast.type.NamedTypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.SeanHelper
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.type.RootResolvedTypeReference
import compiler.handleCyclicInvocation
import compiler.reportings.Reporting

class BoundSupertypeList(
    val context: CTContext,
    val clauses: List<BoundSupertypeDeclaration>,
    getTypeDef: () -> BoundBaseType,
) : SemanticallyAnalyzable {
    private val typeDef by lazy(getTypeDef)

    private val seanHelper = SeanHelper()

    /** the base types that are being extended from, initialized in [semanticAnalysisPhase1] */
    lateinit var baseTypes: List<BoundBaseType>
        private set

    /**
     * becomes meaningful after [semanticAnalysisPhase1]
     */
    var hasCyclicInheritance: Boolean = false

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val reportings = mutableListOf<Reporting>()
            clauses.flatMap { it.semanticAnalysisPhase1() }.forEach(reportings::add)
            baseTypes = clauses.mapNotNull { it.resolvedReference?.baseType }

            // all types that don't declare supertype, except Any itself, inherit from Any implicitly
            if (clauses.isEmpty() && typeDef !== context.swCtx.any) {
                baseTypes = listOf(context.swCtx.any)
            }

            val distinctSuperBaseTypes = mutableSetOf<BoundBaseType>()
            val distinctSupertypes = ArrayList<RootResolvedTypeReference>(clauses.size)
            for (clause in clauses) {
                val resolvedReference = clause.resolvedReference ?: continue
                val cyclicReportings = handleCyclicInvocation(
                    context = this,
                    action = {
                        resolvedReference.baseType.semanticAnalysisPhase1()
                        emptyList()
                    },
                    onCycle = {
                        listOf(Reporting.cyclicInheritance(typeDef, clause))
                    }
                )
                if (cyclicReportings.isNotEmpty()) {
                    reportings.addAll(cyclicReportings)
                    hasCyclicInheritance = true
                    continue
                }

                if (!distinctSuperBaseTypes.add(resolvedReference.baseType)) {
                    reportings.add(Reporting.duplicateSupertype(clause.astNode as NamedTypeReference))
                } else {
                    distinctSupertypes.add(resolvedReference)
                }
            }

            inheritedMemberFunctions = distinctSupertypes
                .asSequence()
                .flatMap { it.memberFunctions }
                .filter { it.declaresReceiver }
                .flatMap { it.overloads }
                .map { InheritedBoundMemberFunction(it, typeDef) }
                .toList()

            inheritedMemberFunctions.forEach {
                reportings.addAll(it.semanticAnalysisPhase1())
            }

            return@phase1 reportings
        }
    }

    /**
     * initialized during [semanticAnalysisPhase2]. Will contain duplicates by [BoundMemberFunction.canonicalName]
     * and parameter count. This is because the overload-set level logic on a derived type also needs to account
     * for the additional [BoundMemberFunction]s in that derived type. So the merging of overloads happens in
     * [BoundBaseType].
     */
    lateinit var inheritedMemberFunctions: List<InheritedBoundMemberFunction>
        private set

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            val reportings = mutableListOf<Reporting>()
            clauses.forEach {
                reportings.addAll(it.semanticAnalysisPhase2())
            }

            inheritedMemberFunctions.forEach {
                reportings.addAll(it.semanticAnalysisPhase2())
            }

            return@phase2 reportings
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            val reportings = mutableListOf<Reporting>()

            clauses.flatMap { it.semanticAnalysisPhase3() }.forEach(reportings::add)
            inheritedMemberFunctions.flatMap { it.semanticAnalysisPhase3() }.forEach(reportings::add)

            return@phase3 reportings
        }
    }
}