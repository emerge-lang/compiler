package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.CanonicalElementName

interface IrBaseType {
    val canonicalName: CanonicalElementName.BaseType
    val parameters: List<Parameter>
    val memberFunctions: Collection<IrOverloadGroup<IrFunction>>

    interface Parameter {
        val name: String
        val variance: IrTypeVariance
        val bound: IrType
    }
}

interface IrIntrinsicType : IrBaseType {
    override val memberFunctions: Collection<IrOverloadGroup<IrFunction>> get() = emptySet()
}

interface IrInterface : IrBaseType

interface IrClass : IrBaseType {
    val memberVariables: List<MemberVariable>
    val constructor: IrImplementedFunction
    val destructor: IrImplementedFunction

    interface MemberVariable {
        val name: String
        val type: IrType
    }
}