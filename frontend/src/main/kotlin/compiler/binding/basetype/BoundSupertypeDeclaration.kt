package compiler.binding.basetype

import compiler.ast.type.TypeReference
import compiler.binding.SeanHelper
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.binding.type.UnresolvedType
import compiler.reportings.Reporting

/**
 * Resembles a supertype declared on a subtype
 */
class BoundSupertypeDeclaration(
    val subtypeContext: CTContext,
    /** @return the subtype */
    private val getTypeDef: () -> BoundBaseType,
    val astNode: TypeReference,
) : SemanticallyAnalyzable {
    private val seanHelper = SeanHelper()
    private lateinit var unfilteredResolved: BoundTypeReference

    /**
     * Is initialized in [semanticAnalysisPhase1]. Remains `null` if [astNode] does not refer directly to a
     * base type (inheriting from a generic type is not allowed).
     */
    var resolvedReference: RootResolvedTypeReference? = null
        get() {
            seanHelper.requirePhase1Done()
            return field
        }
        private set

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return seanHelper.phase1 {
            val reportings = mutableListOf<Reporting>()

            unfilteredResolved = subtypeContext.resolveType(astNode)
            if (unfilteredResolved is RootResolvedTypeReference) {
                resolvedReference = unfilteredResolved as RootResolvedTypeReference
            } else if (unfilteredResolved !is UnresolvedType) {
                reportings.add(Reporting.illegalSupertype(astNode, "can only inherit from interfaces"))
            }

            return@phase1 reportings
        }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return seanHelper.phase2 {
            resolvedReference?.baseType?.semanticAnalysisPhase2()
            unfilteredResolved.validate(TypeUseSite.Irrelevant(astNode.span, getTypeDef()))
        }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return seanHelper.phase3 {
            val reportings = mutableListOf<Reporting>()

            if (!astNode.arguments.isNullOrEmpty()) {
                reportings.add(
                    Reporting.illegalSupertype(
                        astNode,
                        "inheriting from generic types is currently not supported"
                    )
                )
            }

            val localResolvedReference = resolvedReference ?: return@phase3 reportings
            if (localResolvedReference.baseType === subtypeContext.swCtx.unit) {
                return@phase3 reportings
            }

            if (localResolvedReference.baseType.kind != BoundBaseType.Kind.INTERFACE) {
                reportings.add(Reporting.illegalSupertype(astNode, "can only inherit from interfaces"))
            }

            return@phase3 reportings
        }
    }
}