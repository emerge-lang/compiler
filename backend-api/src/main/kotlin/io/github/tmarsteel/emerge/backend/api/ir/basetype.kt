package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

interface IrBaseType {
    val canonicalName: CanonicalElementName.BaseType
    val parameters: List<Parameter>

    /**
     * All member functions that can be found in this type, including inherited ones. Type-check on
     * [IrFullyInheritedMemberFunction] and look at [IrMemberFunction.overrides] to distinguish.
     */
    val memberFunctions: Collection<IrOverloadGroup<IrMemberFunction>>

    interface Parameter {
        val name: String
        val variance: IrTypeVariance
        val bound: IrType
    }
}

interface IrIntrinsicType : IrBaseType {
    override val memberFunctions: Collection<IrOverloadGroup<IrMemberFunction>> get() = emptySet()
}

interface IrInterface : IrBaseType

interface IrClass : IrBaseType {
    val memberVariables: List<MemberVariable>
    val constructor: IrFunction
    val destructor: IrFunction

    interface MemberVariable {
        val name: String
        val type: IrType
    }
}