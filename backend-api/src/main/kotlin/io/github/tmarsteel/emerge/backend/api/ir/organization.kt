package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

interface IrPackage {
    val name: CanonicalElementName.Package
    val functions: Set<IrOverloadGroup<IrFunction>>
    val interfaces: Set<IrInterface>
    val classes: Set<IrClass>
    val variables: Set<IrGlobalVariable>
}

interface IrModule {
    val name: CanonicalElementName.Package
    val packages: Set<IrPackage>
}

interface IrSoftwareContext {
    val modules: Set<IrModule>
}

interface IrGlobalVariable {
    val declaration: IrVariableDeclaration
    val initializer: IrExpression
    val declaredAt: IrSourceLocation
}