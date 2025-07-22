package compiler.binding.basetype

import compiler.InternalCompilerError
import compiler.ast.type.AstIntersectionType
import compiler.ast.type.AstSimpleTypeReference
import compiler.ast.type.TypeReference
import compiler.binding.BoundMemberFunction
import compiler.binding.SeanHelper
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.PartialPreprocessedInheritanceTree
import compiler.binding.type.PreprocessedInheritanceTree
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUnification
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.duplicateSupertype
import compiler.diagnostic.inconsistentTypeArgumentsOnDiamondInheritance
import compiler.lexer.Span
import kotlinext.duplicatesBy

class BoundSupertypeList(
    val context: CTContext,
    val clauses: List<BoundSupertypeDeclaration>,
    getTypeDef: () -> BoundBaseType,
) : SemanticallyAnalyzable {
    private val typeDef by lazy(getTypeDef)

    private val seanHelper = SeanHelper()

    val span: Span = clauses.mapNotNull { it.astNode.span }.reduceOrNull(Span::rangeTo) ?: Span.UNKNOWN

    /** the base types that are being directly extended from **except `emerge.core.Any`!** */
    val directSuperBaseTypes: Set<BoundBaseType> by lazy {
        clauses
            .mapNotNull { it.resolvedReference?.baseType }
            .filter { it != context.swCtx.any }
            .toSet()
    }

    /**
     * initialized in [semanticAnalysisPhase1]
     */
    var preprocessedInheritanceTree: PreprocessedInheritanceTree by seanHelper.resultOfPhase1(allowReassignment = false)
        private set

    /**
     * initialized in [semanticAnalysisPhase1]
     */
    var hasUnresolvedSupertypes: Boolean by seanHelper.resultOfPhase1(allowReassignment = false)
        private set

    /**
     * For example, given:
     *
     *    interface A<T> {}
     *    interface B<E> : A<Array<E>> {}
     *    interface C<K> : B<K> {}
     *
     * when you call `C.getParameterizedSupertype(A)`, it will return `A<Array<K>>`.
     *
     * Combine this with [BoundTypeReference.instantiateAllParameters] and [RootResolvedTypeReference.inherentTypeBindings]
     * to determine e.g. that `C<S32>` is a subtype of `A<Array<S32>>`.
     *
     * @param superBaseType must be a supertype of `this` and must not be equal to `this`
     * @return a [TypeUnification] that maps type parameters in the namespace of [superBaseType] to the bindings it has
     * as a supertype of `this`.
     */
    fun getParameterizedSupertype(superBaseType: BoundBaseType): RootResolvedTypeReference {
        // getInheritanceChains breaks on Any because the implicit subtyping from Any isn't mentioned in superTypes.clauses
        if (superBaseType == context.swCtx.any) {
            return context.swCtx.any.getBoundReferenceAssertNoTypeParameters()
        }

        return preprocessedInheritanceTree.parameterizedSupertypes[superBaseType]
            ?: throw InternalCompilerError("$superBaseType is not a supertype of $typeDef")
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            sean1BuildPreprocessedInheritanceTree(diagnosis)

            clauses
                .mapNotNull { it.resolvedReference }
                .duplicatesBy { it.baseType }
                .values
                .forEach { duped ->
                    diagnosis.duplicateSupertype(duped.first().asAstReference())
                }

            inheritedMemberFunctions = clauses
                .asSequence()
                .filter { it !in preprocessedInheritanceTree.cycles }
                .mapNotNull { it.resolvedReference }
                .flatMap { supertype ->
                    supertype.memberFunctions
                        .asSequence()
                        .filter { it.declaresReceiver }
                        .flatMap { it.overloads }
                        .filter { it.isVirtual ?: false }
                        .map { InheritedBoundMemberFunction(it, typeDef, supertype) }
                        .onEach { it.semanticAnalysisPhase1(diagnosis) }
                        .filter { it.inheritancePreclusionReason == null }
                }
                .toList()
        }
    }

    private fun sean1BuildPreprocessedInheritanceTree(diagnosis: Diagnosis) {
        val partialTrees = ArrayList<PartialPreprocessedInheritanceTree>(clauses.size)
        val cycles = HashSet<BoundSupertypeDeclaration>()
        hasUnresolvedSupertypes = false
        for (clause in clauses) {
            clause.semanticAnalysisPhase1(diagnosis)
            val supertypeRef = clause.resolvedReference
            if (supertypeRef == null) {
                hasUnresolvedSupertypes = true
                continue
            }

            if (clause.isCyclic) {
                cycles.add(clause)
            } else {
                partialTrees.add(supertypeRef.baseType.superTypes.preprocessedInheritanceTree.translateForSubtype(supertypeRef))
            }
            partialTrees.add(PartialPreprocessedInheritanceTree.ofDirectSupertype(supertypeRef))
        }

        val tree = PartialPreprocessedInheritanceTree.merge(partialTrees, cycles)
        tree.inconsistentBindings.forEach { (baseTypeAndParam, inconsistentArgs) ->
            diagnosis.inconsistentTypeArgumentsOnDiamondInheritance(baseTypeAndParam.first, baseTypeAndParam.second, inconsistentArgs, span)
        }

        preprocessedInheritanceTree = tree
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
                is AstSimpleTypeReference -> listOf(supertype)
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