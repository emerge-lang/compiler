package compiler.binding.context

import compiler.binding.BoundFunction
import compiler.binding.BoundVariable
import compiler.binding.type.BaseType
import io.github.tmarsteel.emerge.backend.api.PackageName

class PackageContext(
    val moduleContext: ModuleContext,
    val packageName: PackageName,
) {
    val types: Sequence<BaseType> get() {
        return moduleContext.sourceFiles
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
        return moduleContext.sourceFiles
            .flatMap { it.context.resolveFunction(simpleName, true) }
    }

    fun resolveVariable(simpleName: String): BoundVariable? {
        return moduleContext.sourceFiles
            .asSequence()
            .mapNotNull { it.context.resolveVariable(simpleName, true) }
            .firstOrNull()
    }
}