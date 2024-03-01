package compiler.binding

import compiler.ast.ImportDeclaration
import compiler.binding.context.CTContext
import compiler.binding.context.PackageContext
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName

class BoundImportDeclaration(
    val context: CTContext,
    val declaration: ImportDeclaration,
) : SemanticallyAnalyzable {
    val packageName = DotName(declaration.identifiers.dropLast(1).map { it.value })
    private val simpleNameRaw = declaration.identifiers.last().value
    val isImportAll: Boolean = simpleNameRaw == "*"
    val simpleName: String? = simpleNameRaw.takeUnless { isImportAll }

    private val resolutionResult: ResolutionResult by lazy {
        val packageContext = context.swCtx.getPackage(packageName)
            ?: return@lazy ResolutionResult.Erroneous(Reporting.unresolvablePackageName(packageName, declaration.declaredAt))

        if (isImportAll) {
            return@lazy ResolutionResult.EntirePackage(packageContext)
        }

        val functions = packageContext.resolveFunction(simpleNameRaw)
        if (functions.isNotEmpty()) {
            return@lazy ResolutionResult.Function(simpleNameRaw, functions)
        }

        val baseType = packageContext.resolveBaseType(simpleNameRaw)
        if (baseType != null) {
            return@lazy ResolutionResult.BaseType(baseType)
        }

        val variable = packageContext.resolveVariable(simpleNameRaw)
        if (variable != null) {
            return@lazy ResolutionResult.Variable(variable)
        }

        return@lazy ResolutionResult.Erroneous(Reporting.unresolvableImport(this))
    }

    fun getFunctionOfName(simpleName: String): Collection<BoundFunction>? = when(val result = resolutionResult) {
        is ResolutionResult.EntirePackage -> result.packageContext.resolveFunction(simpleName)
        is ResolutionResult.Function -> if (result.simpleName == simpleName) result.overloads else null
        is ResolutionResult.BaseType,
        is ResolutionResult.Variable,
        is ResolutionResult.Erroneous -> null
    }

    fun getBaseTypeOfName(simpleName: String): compiler.binding.type.BaseType? = when(val result = resolutionResult) {
        is ResolutionResult.EntirePackage -> result.packageContext.resolveBaseType(simpleName)
        is ResolutionResult.BaseType -> result.baseType.takeIf { it.simpleName == simpleName }
        is ResolutionResult.Function,
        is ResolutionResult.Variable,
        is ResolutionResult.Erroneous -> null
    }

    fun getVariableOfName(simpleName: String): BoundVariable? = when(val result = resolutionResult) {
        is ResolutionResult.EntirePackage -> result.packageContext.resolveVariable(simpleName)
        is ResolutionResult.Variable -> result.variable.takeIf { it.name == simpleName }
        is ResolutionResult.BaseType,
        is ResolutionResult.Function,
        is ResolutionResult.Erroneous -> null
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return (resolutionResult as? ResolutionResult.Erroneous)?.errors ?: emptySet()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> = emptySet()

    override fun semanticAnalysisPhase3(): Collection<Reporting> = emptySet()

    private sealed interface ResolutionResult {
        class EntirePackage(val packageContext: PackageContext) : ResolutionResult
        class Function(val simpleName: String, val overloads: Collection<BoundFunction>) : ResolutionResult
        class BaseType(val baseType: compiler.binding.type.BaseType) : ResolutionResult
        class Variable(val variable: BoundVariable) : ResolutionResult
        class Erroneous(error: Reporting) : ResolutionResult {
            val errors = setOf(error)
        }
    }
}