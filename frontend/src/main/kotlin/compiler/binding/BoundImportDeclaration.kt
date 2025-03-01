package compiler.binding

import compiler.ast.ImportDeclaration
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.CTContext
import compiler.binding.context.PackageContext
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.Diagnostic
import io.github.tmarsteel.emerge.common.CanonicalElementName

class BoundImportDeclaration(
    val context: CTContext,
    val declaration: ImportDeclaration,
) : SemanticallyAnalyzable {
    val packageName = CanonicalElementName.Package(declaration.identifiers.dropLast(1).map { it.value })
    private val simpleNameRaw = declaration.identifiers.last().value
    val isImportAll: Boolean = simpleNameRaw == "*"
    val simpleName: String? = simpleNameRaw.takeUnless { isImportAll }

    private val resolutionResult: ResolutionResult by lazy {
        val packageContext = context.swCtx.getPackage(packageName)
            ?: return@lazy ResolutionResult.Erroneous(Diagnostic.unresolvablePackageName(packageName, declaration.declaredAt))

        if (isImportAll) {
            return@lazy ResolutionResult.EntirePackage(packageContext)
        }

        val overloadSets = packageContext.getTopLevelFunctionOverloadSetsBySimpleName(simpleNameRaw)
        if (overloadSets.isNotEmpty()) {
            return@lazy ResolutionResult.OverloadSets(simpleNameRaw, overloadSets)
        }

        val baseType = packageContext.resolveBaseType(simpleNameRaw)
        if (baseType != null) {
            return@lazy ResolutionResult.BaseType(baseType)
        }

        val variable = packageContext.resolveVariable(simpleNameRaw)
        if (variable != null) {
            return@lazy ResolutionResult.Variable(variable)
        }

        return@lazy ResolutionResult.Erroneous(Diagnostic.unresolvableImport(this))
    }

    fun getOverloadSetsBySimpleName(simpleName: String): Collection<BoundOverloadSet<*>> = when(val result = resolutionResult) {
        is ResolutionResult.EntirePackage -> result.packageContext.getTopLevelFunctionOverloadSetsBySimpleName(simpleName)
        is ResolutionResult.OverloadSets -> if (result.simpleName == simpleName) result.sets else emptySet()
        is ResolutionResult.BaseType,
        is ResolutionResult.Variable,
        is ResolutionResult.Erroneous -> emptySet()
    }

    fun getBaseTypeOfName(simpleName: String): BoundBaseType? = when(val result = resolutionResult) {
        is ResolutionResult.EntirePackage -> result.packageContext.resolveBaseType(simpleName)
        is ResolutionResult.BaseType -> result.baseType.takeIf { it.simpleName == simpleName }
        is ResolutionResult.OverloadSets,
        is ResolutionResult.Variable,
        is ResolutionResult.Erroneous -> null
    }

    fun getVariableOfName(simpleName: String): BoundVariable? = when(val result = resolutionResult) {
        is ResolutionResult.EntirePackage -> result.packageContext.resolveVariable(simpleName)
        is ResolutionResult.Variable -> result.variable.takeIf { it.name == simpleName }
        is ResolutionResult.BaseType,
        is ResolutionResult.OverloadSets,
        is ResolutionResult.Erroneous -> null
    }

    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        (resolutionResult as? ResolutionResult.Erroneous)?.errors?.forEach(diagnosis::add)
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) = Unit

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        val lastIdentifierAt = declaration.identifiers.last().span
        when (val result = resolutionResult) {
            is ResolutionResult.Variable -> {
                if (result.variable.kind.allowsVisibility) {
                    result.variable.visibility.validateAccessFrom(lastIdentifierAt, result.variable, diagnosis)
                }
            }
            is ResolutionResult.OverloadSets -> {
                val accessDiagnosis = result.sets.asSequence()
                    .flatMap { it.overloads }
                    .map {
                        val subDiagnosis = CollectingDiagnosis()
                        it.attributes.visibility.validateAccessFrom(lastIdentifierAt, it, subDiagnosis)
                        subDiagnosis
                    }
                val noneAccessible = accessDiagnosis.all { it.nErrors > 0uL }
                if (noneAccessible) {
                    accessDiagnosis.filter { it.nErrors > 0uL }.first().replayOnto(diagnosis)
                }
            }
            is ResolutionResult.BaseType -> {
                result.baseType.validateAccessFrom(lastIdentifierAt, diagnosis)
            }
            else -> { /* nothing to do */ }
        }
    }

    private sealed interface ResolutionResult {
        class EntirePackage(val packageContext: PackageContext) : ResolutionResult
        class OverloadSets(val simpleName: String, val sets: Collection<BoundOverloadSet<*>>) : ResolutionResult
        class BaseType(val baseType: BoundBaseType) : ResolutionResult
        class Variable(val variable: BoundVariable) : ResolutionResult
        class Erroneous(error: Diagnostic) : ResolutionResult {
            val errors = setOf(error)
        }
    }
}