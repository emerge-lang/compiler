package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.DotName

interface IrBaseType {
    val fqn: DotName
    val parameters: List<Parameter>

    interface Parameter {
        val name: String
        val variance: IrTypeVariance
        val bound: IrType
    }
}

interface IrIntrinsicType : IrBaseType

interface IrClass : IrBaseType {
    val memberVariables: List<MemberVariable>
    val memberFunctions: Collection<IrOverloadGroup<IrFunction>>
    val constructor: IrImplementedFunction
    val destructor: IrImplementedFunction

    interface MemberVariable {
        val name: String
        val type: IrType
    }
}