package compiler.binding.basetype

import compiler.ast.type.AstSimpleTypeReference
import compiler.ast.type.AstWildcardTypeArgument
import compiler.binding.SeanHelper
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeArgument
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.ErroneousType
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.cyclicInheritance
import compiler.diagnostic.illegalSupertype
import compiler.diagnostic.immediateWildcardTypeArgumentOnSupertype
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
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            if (!isCyclic) {
                resolvedReference?.baseType?.semanticAnalysisPhase2(diagnosis)
            }

            unfilteredResolved.validate(TypeUseSite.Irrelevant(astNode.span, getTypeDef()), diagnosis)

            resolvedReference?.inherentTypeBindings?.bindings
                ?.filter { (_, arg) -> (arg as BoundTypeArgument).astNode is AstWildcardTypeArgument }
                ?.forEach { (param, arg) ->
                    diagnosis.immediateWildcardTypeArgumentOnSupertype((arg as BoundTypeArgument).astNode, param.astNode)
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