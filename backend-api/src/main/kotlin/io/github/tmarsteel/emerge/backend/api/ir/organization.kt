package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.PackageName

interface IrPackage {
    val name: PackageName
    val functions: Set<IrOverloadGroup<IrFunction>>
    val classes: Set<IrClass>
    val variables: Set<IrGlobalVariable>
}

interface IrModule {
    val name: PackageName
    val packages: Set<IrPackage>
}

interface IrSoftwareContext {
    val modules: Set<IrModule>
}

interface IrGlobalVariable {
    val declaration: IrVariableDeclaration
    val initializer: IrExpression
}