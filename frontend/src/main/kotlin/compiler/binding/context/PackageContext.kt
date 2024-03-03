package compiler.binding.context

import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVariable
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.type.BaseType
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName

class PackageContext(
    val moduleContext: ModuleContext,
    val packageName: DotName,
) : SemanticallyAnalyzable {
    val sourceFiles: Sequence<SourceFile> = sequence {
        yieldAll(moduleContext.sourceFiles)
    }.filter { it.packageName == packageName }

    val types: Sequence<BaseType> get() {
        return sourceFiles
            .filter { it.packageName == packageName }
            .flatMap { it.context.types }
    }

    private val typeByNameCache = HashMap<String, BaseType>()
    fun resolveBaseType(simpleName: String): BaseType? {
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

    private val overloadSetsBySimpleName: Map<String, Collection<BoundOverloadSet>> by lazy {
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
                        BoundOverloadSet(packageName.plus(name), parameterCount, overloads)
                    }
            }
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return overloadSetsBySimpleName.values
            .flatten()
            .flatMap { it.semanticAnalysisPhase1() }
    }

    fun getTopLevelFunctionOverloadSetsBySimpleName(simpleName: String): Collection<BoundOverloadSet> {
        return overloadSetsBySimpleName[simpleName] ?: emptySet()
    }

    val allToplevelFunctionOverloadSets: Sequence<BoundOverloadSet> = sequence { yieldAll(overloadSetsBySimpleName.values) }.flatten()

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return (sourceFiles.flatMap { it.semanticAnalysisPhase2() } +
                overloadSetsBySimpleName.values.flatten().flatMap { it.semanticAnalysisPhase2() })
            .toList()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return (sourceFiles.flatMap { it.semanticAnalysisPhase3() } +
                overloadSetsBySimpleName.values.flatten().flatMap { it.semanticAnalysisPhase3() })
            .toList()
    }

    override fun equals(other: Any?): Boolean {
        return other != null && other::class == PackageContext::class && (other as PackageContext).packageName == this.packageName
    }

    override fun hashCode() = packageName.hashCode()
}