package compiler.binding.context

import compiler.binding.type.BaseType
import io.github.tmarsteel.emerge.backend.api.PackageName

class PackageContext(
    val module: ModuleContext,
    val packageName: PackageName,
) {
    val types: Sequence<BaseType> get() {
        return module.sourceFiles
            .asSequence()
            .filter { it.packageName == packageName }
            .flatMap { it.context.types }
    }
}