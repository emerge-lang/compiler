package compiler.binding.context

import compiler.PackageName
import compiler.binding.type.BaseType

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