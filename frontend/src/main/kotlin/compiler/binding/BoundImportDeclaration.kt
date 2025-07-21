package compiler.binding

import compiler.ast.AstImportDeclaration
import compiler.binding.basetype.BoundBaseType
import compiler.binding.context.CTContext
import compiler.binding.context.PackageContext
import compiler.diagnostic.CollectingDiagnosis
import compiler.diagnostic.Diagnosis
import compiler.diagnostic.UnresolvableImportDiagnostic
import compiler.diagnostic.UnresolvablePackageNameDiagnostic
import compiler.lexer.IdentifierToken
import compiler.lexer.Operator
import io.github.tmarsteel.emerge.common.CanonicalElementName

sealed class BoundImportDeclaration(
    val context: CTContext,
    val declaration: AstImportDeclaration,
) : SemanticallyAnalyzable {
    val packageName = CanonicalElementName.Package(declaration.packageIdentifiers.map { it.value })
    protected val packageContext: PackageContext? by lazy {
        context.swCtx.getPackage(packageName)
    }

    abstract fun getOverloadSetsBySimpleName(simpleName: String): Collection<BoundOverloadSet<*>>
    abstract fun getBaseTypeOfName(simpleName: String): BoundBaseType?
    abstract fun getVariableOfName(simpleName: String): BoundVariable?
    abstract fun isUnresolvedAndAppliesToSimpleName(simpleName: String): Boolean

    final override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
        if (packageContext == null) {
            diagnosis.add(UnresolvablePackageNameDiagnostic(packageName, declaration.declaredAt))
            return
        }

        innerSemanticAnalysisPhase1(diagnosis)
    }

    protected abstract fun innerSemanticAnalysisPhase1(diagnosis: Diagnosis)

    companion object {
        /**
         * The value that triggers a wildcard import (all exported elements of the package)
         */
        val WILDCARD_SYMBOL = Operator.TIMES.text

        operator fun invoke(context: CTContext, declaration: AstImportDeclaration): BoundImportDeclaration = when {
            declaration.symbols.size == 1 -> {
                val singleSymbol = declaration.symbols.single()
                if (singleSymbol.value == WILDCARD_SYMBOL) {
                    BoundEntirePackageImportDeclaration(context, declaration)
                } else {
                    BoundSingleSymbolImportDeclaration(context, declaration, singleSymbol)
                }
            }
            else -> {
                check(declaration.symbols.size > 1)
                BoundMultipleSymbolsImportDeclaration(context, declaration)
            }
        }
    }
}

class BoundSingleSymbolImportDeclaration(
    context: CTContext,
    declaration: AstImportDeclaration,
    private val simpleNameRaw: IdentifierToken,
) : BoundImportDeclaration(context, declaration) {
    val simpleName: String = simpleNameRaw.value
    private val resolutionResult: ResolutionResult? by lazy {
        packageContext?.let { localPkgCtx ->
            resolveSingleSymbolInPackage(localPkgCtx, simpleNameRaw)
        }
    }

    override fun innerSemanticAnalysisPhase1(diagnosis: Diagnosis) {
        resolutionResult?.semanticAnalysisPhase1(diagnosis)
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        resolutionResult?.semanticAnalysisPhase2(diagnosis)
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        resolutionResult?.semanticAnalysisPhase3(diagnosis)
    }

    override fun getOverloadSetsBySimpleName(simpleName: String): Collection<BoundOverloadSet<*>> = when(val result = resolutionResult) {
        is ResolutionResult.OverloadSets -> if (result.simpleNameToken.value == simpleName) result.sets else emptySet()
        is ResolutionResult.BaseType,
        is ResolutionResult.Variable,
        is ResolutionResult.SymbolNotDefined,
        null -> emptySet()
    }

    override fun getBaseTypeOfName(simpleName: String): BoundBaseType? = when(val result = resolutionResult) {
        is ResolutionResult.BaseType -> result.baseType.takeIf { it.simpleName == simpleName }
        is ResolutionResult.OverloadSets,
        is ResolutionResult.Variable,
        is ResolutionResult.SymbolNotDefined,
        null -> null
    }

    override fun getVariableOfName(simpleName: String): BoundVariable? = when(val result = resolutionResult) {
        is ResolutionResult.Variable -> result.variable.takeIf { it.name == simpleName }
        is ResolutionResult.BaseType,
        is ResolutionResult.OverloadSets,
        is ResolutionResult.SymbolNotDefined,
        null -> null
    }

    override fun isUnresolvedAndAppliesToSimpleName(simpleName: String): Boolean {
        return this.simpleName == simpleName && (resolutionResult == null || resolutionResult?.isErroneous == true)
    }
}

class BoundEntirePackageImportDeclaration(
    context: CTContext,
    declaration: AstImportDeclaration,
) : BoundImportDeclaration(context, declaration) {
    override fun getOverloadSetsBySimpleName(simpleName: String): Collection<BoundOverloadSet<*>> {
        return packageContext?.getTopLevelFunctionOverloadSetsBySimpleName(simpleName) ?: emptySet()
    }

    override fun getBaseTypeOfName(simpleName: String): BoundBaseType? {
        return packageContext?.resolveBaseType(simpleName)
    }

    override fun getVariableOfName(simpleName: String): BoundVariable? {
        return packageContext?.resolveVariable(simpleName)
    }

    override fun innerSemanticAnalysisPhase1(diagnosis: Diagnosis) {
        // nothing to do
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        // nothing to do
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        // nothing to do
    }

    override fun isUnresolvedAndAppliesToSimpleName(simpleName: String): Boolean {
        return packageContext == null
    }
}

class BoundMultipleSymbolsImportDeclaration(
    context: CTContext,
    declaration: AstImportDeclaration,
) : BoundImportDeclaration(context, declaration) {
    private val resolutionResultsBySimpleName: Map<String, ResolutionResult> by lazy {
        packageContext?.let { localPkgCtx ->
            declaration.symbols.associate {
                val result = resolveSingleSymbolInPackage(localPkgCtx, it)
                it.value to result
            }
        } ?: emptyMap()
    }

    override fun innerSemanticAnalysisPhase1(diagnosis: Diagnosis) {
        resolutionResultsBySimpleName.values.forEach {
            it.semanticAnalysisPhase1(diagnosis)
        }
    }

    override fun getOverloadSetsBySimpleName(simpleName: String): Collection<BoundOverloadSet<*>> {
        return when (val result = resolutionResultsBySimpleName[simpleName]) {
            is ResolutionResult.OverloadSets -> result.sets
            is ResolutionResult.BaseType,
            is ResolutionResult.Variable,
            is ResolutionResult.SymbolNotDefined,
            null -> emptySet()
        }
    }

    override fun getBaseTypeOfName(simpleName: String): BoundBaseType? {
        return when (val result = resolutionResultsBySimpleName[simpleName]) {
            is ResolutionResult.BaseType -> result.baseType
            is ResolutionResult.OverloadSets,
            is ResolutionResult.Variable,
            is ResolutionResult.SymbolNotDefined,
            null -> null
        }
    }

    override fun getVariableOfName(simpleName: String): BoundVariable? {
        return when (val result = resolutionResultsBySimpleName[simpleName]) {
            is ResolutionResult.Variable -> result.variable
            is ResolutionResult.BaseType,
            is ResolutionResult.OverloadSets,
            is ResolutionResult.SymbolNotDefined,
            null -> null
        }
    }

    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) {
        resolutionResultsBySimpleName.values.forEach {
            it.semanticAnalysisPhase2(diagnosis)
        }
    }

    override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
        resolutionResultsBySimpleName.values.forEach {
            it.semanticAnalysisPhase3(diagnosis)
        }
    }

    override fun isUnresolvedAndAppliesToSimpleName(simpleName: String): Boolean {
        return resolutionResultsBySimpleName[simpleName]?.isErroneous == true
    }
}

private fun resolveSingleSymbolInPackage(packageContext: PackageContext, simpleNameToken: IdentifierToken): ResolutionResult {
    val overloadSets = packageContext.getTopLevelFunctionOverloadSetsBySimpleName(simpleNameToken.value)
    if (overloadSets.isNotEmpty()) {
        return ResolutionResult.OverloadSets(simpleNameToken, overloadSets)
    }

    val baseType = packageContext.resolveBaseType(simpleNameToken.value)
    if (baseType != null) {
        return ResolutionResult.BaseType(simpleNameToken, baseType)
    }

    val variable = packageContext.resolveVariable(simpleNameToken.value)
    if (variable != null) {
        return ResolutionResult.Variable(simpleNameToken, variable)
    }

    return ResolutionResult.SymbolNotDefined(packageContext.packageName, simpleNameToken)
}

private sealed interface ResolutionResult : SemanticallyAnalyzable {
    override fun semanticAnalysisPhase1(diagnosis: Diagnosis) = Unit
    override fun semanticAnalysisPhase2(diagnosis: Diagnosis) = Unit
    val isErroneous: Boolean

    class OverloadSets(val simpleNameToken: IdentifierToken, val sets: Collection<BoundOverloadSet<*>>) : ResolutionResult {
        override val isErroneous = false

        override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
            val accessDiagnosis = sets.asSequence()
                .flatMap { it.overloads }
                .map {
                    val subDiagnosis = CollectingDiagnosis()
                    it.attributes.visibility.validateAccessFrom(simpleNameToken.span, it, subDiagnosis)
                    subDiagnosis
                }
            val noneAccessible = accessDiagnosis.all { it.nErrors > 0uL }
            if (noneAccessible) {
                accessDiagnosis.filter { it.nErrors > 0uL }.first().replayOnto(diagnosis)
            }
        }
    }

    class BaseType(val simpleNameToken: IdentifierToken, val baseType: BoundBaseType) : ResolutionResult {
        override val isErroneous = false

        override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
            baseType.validateAccessFrom(simpleNameToken.span, diagnosis)
        }
    }

    class Variable(val simpleNameToken: IdentifierToken, val variable: BoundVariable) : ResolutionResult {
        override val isErroneous = false

        override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
            if (variable.kind.allowsVisibility) {
                variable.visibility.validateAccessFrom(simpleNameToken.span, variable, diagnosis)
            }
        }
    }

    class SymbolNotDefined(val packageName: CanonicalElementName.Package, val simpleNameToken: IdentifierToken) : ResolutionResult {
        override val isErroneous = true

        override fun semanticAnalysisPhase1(diagnosis: Diagnosis) {
            diagnosis.add(UnresolvableImportDiagnostic(packageName, simpleNameToken))
        }

        override fun semanticAnalysisPhase3(diagnosis: Diagnosis) {
            // nothing to do, no access check can be done
        }
    }
}