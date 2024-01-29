package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.DotName

interface IrPackage {
    val name: DotName
    val functions: Set<IrOverloadGroup<IrFunction>>
    val structs: Set<IrStruct>
}

interface IrModule {
    val name: DotName
    val packages: Set<IrPackage>
}

interface IrSoftwareContext {
    val modules: Set<IrModule>
}