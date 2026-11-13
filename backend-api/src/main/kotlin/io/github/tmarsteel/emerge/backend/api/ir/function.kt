package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.common.CanonicalElementName

interface IrFunction {
    val canonicalName: CanonicalElementName.Function
    val parameters: List<IrVariableDeclaration>
    val declaresReceiver: Boolean
    val returnType: IrType
    val isNothrow: Boolean
    val isExternalC: Boolean

    /**
     * Iff [isExternalC], the name of the C symbol the function binds to: the name given in the declaration
     * (`external(C, "__errno_location")`), the simple name of the function otherwise.
     */
    val externalSymbolName: String?

    /**
     * The type parameters this function receives the runtime type information for, as hidden arguments of type
     * `const emerge.core.reflection.Type` that follow [parameters] in this order. These are the type parameters
     * declared on the function itself; for constructors, the type parameters of the class. Type parameters of the
     * class are not passed to member functions that declare a receiver, those are stored in the receiver
     * (see [IrClass.typeParameterFields]).
     */
    val typeParameters: List<IrBaseType.Parameter>

    /**
     * the implementation of this function; null iff
     * * [isExternalC]
     * * is intrinsic
     * * is abstract (declared on interface without body)
     */
    val body: IrCodeChunk?

    val declaredAt: IrSourceLocation
}

interface IrBaseTypeFunction : IrFunction {
    val ownerBaseType: IrBaseType
}

interface IrConstructor : IrBaseTypeFunction {

}

interface IrMemberFunction : IrBaseTypeFunction {
    /**
     * If this is a virtual function override, this points to the functions that are being overridden.
     */
    val overrides: Set<IrMemberFunction>

    /**
     * True if this function can be dynamically dispatched on its receiver (need not always be, though!). This is
     * false e.g. for type functions (don't declare a receiver parameter)
     */
    val supportsDynamicDispatch: Boolean
}

/**
 * Denotes that this member function is declared in a supertype, too.
 */
sealed interface IrInheritedMemberFunction : IrMemberFunction {
    val superFunction: IrMemberFunction
}

/**
 * Denotes that this member function is fully reused from the supertype, so the compilation result of the
 * supertype function could be re-used to save on program size.
 */
interface IrFullyInheritedMemberFunction : IrInheritedMemberFunction

/**
 * Denotes that the implementation of this member function should be delegated to a nested object
 * that implements the same supertype
 */
interface IrDelegatingMemberFunction : IrInheritedMemberFunction {
    /**
     * The delegation target. Is guaranteed to
     * * be initialized to a non-null value during object construction
     * * refer to an object that implements the same supertype as [superFunction].`ownerBaseType`
     */
    val delegatesTo: IrClass.Field
}

/**
 * A group of function declarations, all with the same name and parameter count (receiver/self is always counted)
 */
interface IrOverloadGroup<out T> {
    val canonicalName: CanonicalElementName.Function
    val parameterCount: Int
    val overloads: Set<T>
}