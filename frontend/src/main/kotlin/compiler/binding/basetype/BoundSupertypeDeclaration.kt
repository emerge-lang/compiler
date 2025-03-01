package compiler.binding.basetype

import compiler.ast.type.TypeReference
import compiler.binding.SeanHelper
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.context.CTContext
import compiler.binding.type.BoundTypeReference
import compiler.binding.type.RootResolvedTypeReference
import compiler.binding.type.TypeUseSite
import compiler.binding.type.UnresolvedType
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import compiler.diagnostic.illegalSupertype

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

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        return seanHelper.phase1(diagnosis) {

            unfilteredResolved = subtypeContext.resolveType(astNode)
            if (unfilteredResolved is RootResolvedTypeReference) {
                resolvedReference = unfilteredResolved as RootResolvedTypeReference
            } else if (unfilteredResolved !is UnresolvedType) {
                diagnosis.illegalSupertype(astNode, "can only inherit from interfaces")
            }
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        return seanHelper.phase2(diagnosis) {
            resolvedReference?.baseType?.semanticAnalysisPhase2(diagnosis)
            unfilteredResolved.validate(TypeUseSite.Irrelevant(astNode.span, getTypeDef()), diagnosis)
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        return seanHelper.phase3(diagnosis) {

            if (!astNode.arguments.isNullOrEmpty()) {
                diagnosis.illegalSupertype(astNode, "inheriting from generic types is currently not supported")
            }

            val localResolvedReference = resolvedReference ?: return@phase3
            if (localResolvedReference.baseType === subtypeContext.swCtx.unit) {
                return@phase3
            }

            if (localResolvedReference.baseType.kind != BoundBaseType.Kind.INTERFACE) {
                diagnosis.illegalSupertype(astNode, "can only inherit from interfaces")
            }
        }
    }
}