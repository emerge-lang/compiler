package compiler.binding.context

import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.binding.SemanticallyAnalyzable
import compiler.binding.expression.validateOverloadSet
import compiler.binding.type.BaseType
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.DotName

class PackageContext(
    val packageName: DotName,
    val sourceFiles: Collection<SourceFile>,
) : SemanticallyAnalyzable {
    val types: Sequence<BaseType> get() {
        return sourceFiles
            .asSequence()
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

    fun resolveFunction(simpleName: String): Collection<BoundFunction> {
        return sourceFiles
            .flatMap { it.context.resolveFunction(simpleName, true) }
    }

    fun resolveVariable(simpleName: String): BoundVariable? {
        return sourceFiles
            .asSequence()
            .mapNotNull { it.context.resolveVariable(simpleName, true) }
            .firstOrNull()
    }

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return emptySet()
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return emptySet()
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return sourceFiles
            .flatMap { it.context.functions }
            .groupBy { Pair(it.name, it.parameters.parameters.size) }
            .values
            .flatMap { it.validateOverloadSet() }
    }

    override fun equals(other: Any?): Boolean {
        return other != null && other::class == PackageContext::class && (other as PackageContext).packageName == this.packageName
    }

    override fun hashCode() = packageName.hashCode()
}