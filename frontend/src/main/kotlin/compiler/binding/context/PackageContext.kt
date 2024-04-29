package compiler.binding.context

import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVariable
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.basetype.BoundBaseTypeDefinition
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

class PackageContext(
    val moduleContext: ModuleContext,
    val packageName: CanonicalElementName.Package,
) : SemanticallyAnalyzable {
    val sourceFiles: Sequence<SourceFile> = sequence {
        yieldAll(moduleContext.sourceFiles)
    }.filter { it.packageName == packageName }

    val types: Sequence<BoundBaseTypeDefinition> get() {
        return sourceFiles
            .filter { it.packageName == packageName }
            .flatMap { it.context.types }
    }

    private val typeByNameCache = HashMap<String, BoundBaseTypeDefinition>()
    fun resolveBaseType(simpleName: String): BoundBaseTypeDefinition? {
        typeByNameCache[simpleName]?.let { return it }
        val type = types.find { it.simpleName == simpleName } ?: return null
        typeByNameCache[simpleName] = type
        return type
    }

    fun resolveVariable(simpleName: String): BoundVariable? {
        return sourceFiles
            .mapNotNull { it.context.resolveVariable(simpleName, true) }
            .firstOrNull()
    }

    private val overloadSetsBySimpleName: Map<String, Collection<BoundOverloadSet<*>>> by lazy {
        /*
        this HAS to be lazy, because:
        * it cannot be initialized together with the package context, as not all contents of the package are known at that point in time
        * it cannot be initialized in semanticAnalysisPhase1 because other code that depends on this package might do phase 1
          earlier; definitely the case for cyclic imports
         */
        sourceFiles
            .flatMap { it.context.functions }
            .groupBy { it.name }
            .mapValues { (name, overloads) ->
                overloads
                    .groupBy { it.parameters.parameters.size }
                    .map { (parameterCount, overloads) ->
                        BoundOverloadSet(overloads.first().canonicalName, parameterCount, overloads)
                    }
            }
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return overloadSetsBySimpleName.values
            .flatten()
            .flatMap { it.semanticAnalysisPhase1() }
    }

    fun getTopLevelFunctionOverloadSetsBySimpleName(simpleName: String): Collection<BoundOverloadSet<*>> {
        return overloadSetsBySimpleName[simpleName] ?: emptySet()
    }

    val allToplevelFunctionOverloadSets: Sequence<BoundOverloadSet<*>> = sequence { yieldAll(overloadSetsBySimpleName.values) }.flatten()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        sourceFiles.flatMap { it.semanticAnalysisPhase2() }.forEach(reportings::add)
        overloadSetsBySimpleName.values.flatten().flatMap { it.semanticAnalysisPhase2() }.forEach(reportings::add)

        return reportings
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        val reportings = mutableListOf<Reporting>()
        sourceFiles.flatMap { it.semanticAnalysisPhase3() }.forEach(reportings::add)
        overloadSetsBySimpleName.values.flatten().flatMap { it.semanticAnalysisPhase3() }.forEach(reportings::add)

        types
            .asSequence()
            .groupBy { it.simpleName }
            .filter { (_, types) -> types.size > 1 }
            .forEach { (simpleName, duplicateTypes) ->
                // TODO: remove filter as soon as all basetypes are in emerge source
                val dupes = duplicateTypes.filterIsInstance<BoundBaseTypeDefinition>()
                reportings.add(Reporting.duplicateBaseTypes(packageName, dupes))
            }

        return reportings
    }

    override fun equals(other: Any?): Boolean {
        return other != null && other::class == PackageContext::class && (other as PackageContext).packageName == this.packageName
    }

    override fun hashCode() = packageName.hashCode()
}