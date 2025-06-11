package compiler.binding.basetype

import compiler.ast.type.AstIntersectionType
import compiler.ast.type.NamedTypeReference
import compiler.ast.type.TypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.SeanHelper
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.type.RootResolvedTypeReference
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.cyclicInheritance
import compiler.diagnostic.duplicateSupertype
import compiler.handleCyclicInvocation

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

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            clauses.forEach { it.semanticAnalysisPhase1(diagnosis) }
            baseTypes = clauses.mapNotNull { it.resolvedReference?.baseType }

            // all types that don't declare supertype, except Any itself, inherit from Any implicitly
            if (clauses.isEmpty() && typeDef !== context.swCtx.any) {
                baseTypes = listOf(context.swCtx.any)
            }

            val distinctSuperBaseTypes = mutableSetOf<BoundBaseType>()
            val distinctSupertypes = ArrayList<RootResolvedTypeReference>(clauses.size)
            for (clause in clauses) {
                val resolvedReference = clause.resolvedReference ?: continue
                handleCyclicInvocation(
                    context = this,
                    action = {
                        resolvedReference.baseType.semanticAnalysisPhase1(diagnosis)
                    },
                    onCycle = {
                        diagnosis.cyclicInheritance(typeDef, clause)
                        hasCyclicInheritance = true
                    }
                )
                if (hasCyclicInheritance) {
                    continue
                }

                if (!distinctSuperBaseTypes.add(resolvedReference.baseType)) {
                    diagnosis.duplicateSupertype(clause.astNode)
                } else {
                    distinctSupertypes.add(resolvedReference)
                }
            }

            inheritedMemberFunctions = distinctSupertypes
                .asSequence()
                .flatMap { supertype ->
                    supertype.memberFunctions
                        .asSequence()
                        .filter { it.declaresReceiver }
                        .flatMap { it.overloads }
                        .map { InheritedBoundMemberFunction(it, typeDef, supertype) }
                }
                .toList()

            inheritedMemberFunctions.forEach {
                it.semanticAnalysisPhase1(diagnosis)
            }
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

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            clauses.forEach {
                it.semanticAnalysisPhase2(diagnosis)
            }

            inheritedMemberFunctions.forEach {
                it.semanticAnalysisPhase2(diagnosis)
            }

            /*
            if this derived type inherits form the same indirect supertype (I) through multiple intermediate supertypes,
            and if I is parametric, then the parameters for I could differ on when following the different inheritance chains
            if so, that constitutes a compile-time error;
            TODO: diagnose this situation
             */
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            clauses.forEach { it.semanticAnalysisPhase3(diagnosis) }
            inheritedMemberFunctions.forEach { it.semanticAnalysisPhase3(diagnosis) }
        }
    }

    companion object {
        fun bindSingleSupertype(
            supertype: TypeReference?,
            typeRootContext: CTContext,
            typeDefAccessor: () -> BoundBaseType,
        ): BoundSupertypeList {
            val astSupertypes = when (supertype) {
                is NamedTypeReference -> listOf(supertype)
                is AstIntersectionType -> supertype.components
                null -> emptyList()
            }
            return BoundSupertypeList(
                typeRootContext,
                astSupertypes.map {
                    BoundSupertypeDeclaration(typeRootContext, typeDefAccessor, it)
                },
                typeDefAccessor,
            )
        }
    }
}