package compiler.binding.basetype

import compiler.ast.type.AstSimpleTypeReference
import compiler.ast.type.AstWildcardTypeArgument
import compiler.ast.type.TypeVariance
import compiler.binding.SeanHelper
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.ErroneousType
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.diagnostic.*
import compiler.handleCyclicInvocation
import kotlin.properties.Delegates

/**
 * Resembles a supertype declared on a subtype
 */
class BoundSupertypeDeclaration(
    val subtypeContext: CTContext,
    /** @return the subtype */
    private val getTypeDef: () -> BoundBaseType,
    val astNode: AstSimpleTypeReference,
) : SemanticallyAnalyzable {
    private val seanHelper = SeanHelper()
    private val unfilteredResolved: BoundTypeReference by lazy {
        subtypeContext.resolveType(astNode)
    }

    /**
     * Is initialized in [semanticAnalysisPhase1]. Remains `null` if [astNode] does not refer directly to a
     * base type (inheriting from a generic type is not allowed).
     */
    val resolvedReference: RootResolvedTypeReference? by lazy {
        unfilteredResolved as? RootResolvedTypeReference
    }

    /**
     * Whether this supertype relation creates a cycle; initialized during [semanticAnalysisPhase1].
     */
    var isCyclic: Boolean by Delegates.notNull()
        private set

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {
            isCyclic = handleCyclicInvocation(
                context = this,
                action = {
                    resolvedReference?.baseType?.semanticAnalysisPhase1(diagnosis)
                    false
                },
                onCycle = {
                    diagnosis.cyclicInheritance(getTypeDef(), this)
                    true
                }
            )

            if (unfilteredResolved !is RootResolvedTypeReference && unfilteredResolved !is ErroneousType) {
                diagnosis.illegalSupertype(astNode, "can only inherit from interfaces")
            }

            // the inherited member functions are checked against this supertype as declared (InheritedBoundMemberFunction),
            // still in phase 1 of the subtype. That unifies the type arguments, which needs the inheritance trees of all
            // base types mentioned in them. The subtype itself (class C : I<C>) is being analyzed right now.
            resolvedReference?.arguments?.forEach { argument ->
                val superBaseTypes = mutableSetOf<BoundBaseType>()
                handleCyclicInvocation(
                    context = this,
                    action = { argument.type.collectBaseTypes(superBaseTypes) },
                    onCycle = {},
                )
                superBaseTypes.forEach { baseType ->
                    if (!baseType.isPhase1InProgress) {
                        baseType.semanticAnalysisPhase1(diagnosis)
                    }
                }
            }
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            if (!isCyclic) {
                resolvedReference?.baseType?.semanticAnalysisPhase2(diagnosis)
            }

            unfilteredResolved.validate(TypeUseSite.Irrelevant(astNode.span, getTypeDef()), diagnosis)

            val parameters = resolvedReference?.baseType?.typeParameters.orEmpty()
            resolvedReference?.arguments.orEmpty().zip(parameters).forEach { (arg, param) ->
                if (arg.astNode is AstWildcardTypeArgument) {
                    diagnosis.immediateWildcardTypeArgumentOnSupertype(arg.astNode, param.astNode)
                } else if (arg.variance != TypeVariance.UNSPECIFIED) {
                    diagnosis.immediateVariantTypeArgumentOnSupertype(arg.astNode)
                }
            }
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {
            val localResolvedReference = resolvedReference ?: return@phase3
            if (localResolvedReference.baseType === subtypeContext.swCtx.unit) {
                return@phase3
            }

            if (!localResolvedReference.baseType.kind.allowsSubtypes) {
                diagnosis.illegalSupertype(astNode, "can only inherit from interfaces")
            }
        }
    }
}
