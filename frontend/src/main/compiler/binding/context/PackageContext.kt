package compiler.binding.context

import compiler.PackageName

class PackageContext(
    val module: ModuleContext,
    val packageName: PackageName,
)