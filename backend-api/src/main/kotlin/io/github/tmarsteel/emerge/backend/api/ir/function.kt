package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

interface IrFunction {
    val canonicalName: CanonicalElementName.Function
    val parameters: List<IrVariableDeclaration>
    val returnType: IrType
    val isExternalC: Boolean

    /**
     * the implementation of this function; null iff
     * * [isExternalC]
     * * is intrinsic
     * * is abstract (declared on interface without body)
     */
    val body: IrCodeChunk?
}

interface IrMemberFunction : IrFunction {
    /**
     * If this is a virtual function override, this points to the function in the supertype that is being overridden.
     */
    val overrides: IrMemberFunction?

    /**
     * True if this function can be dynamically dispatched on its receiver (need not always be, though!). This is
     * false e.g. for type functions (don't declare a receiver parameter)
     */
    val supportsDynamicDispatch: Boolean

    val declaredOn: IrBaseType
}

/**
 * Denotes that this member function is fully reused from the supertype, so the compilation result of the
 * supertype function could be re-used to save on program size.
 */
interface IrFullyInheritedMemberFunction : IrMemberFunction {
    val superFunction: IrMemberFunction
}

/**
 * A group of function declarations, all with the same name and parameter count (receiver/self is always counted)
 */
interface IrOverloadGroup<out T> {
    val canonicalName: CanonicalElementName.Function
    val parameterCount: Int
    val overloads: Set<T>
}