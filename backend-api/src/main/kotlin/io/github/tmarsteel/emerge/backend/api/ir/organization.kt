package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.common.CanonicalElementName

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

/**
 * A variable of which every thread has its own instance. The backend must make sure that in each thread
 * * the [initializer] has been evaluated and its value written to the variable before the first access to the
 *   variable, be it a read or a write. An [initializer] can access any other global variable, also through the
 *   functions it invokes; the frontend doesn't provide an order in which the initializers can be evaluated upfront.
 * * the [initializer] is evaluated at most once
 * * all global variables are initialized before any code of the thread other than initializers runs
 *
 * If an [initializer] depends on the value of its own variable, or if it throws, the program cannot continue.
 */
interface IrGlobalVariable {
    val name: CanonicalElementName.Global
    val declaration: IrVariableDeclaration

    /**
     * The frontend doesn't emit an [IrAssignmentStatement] for the initial value of a global variable; writing
     * the value of this expression to the variable is up to the backend.
     */
    val initializer: IrExpression
    val declaredAt: IrSourceLocation
}