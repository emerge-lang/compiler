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
    val members: List<MemberVariable>
    val constructors: Set<IrOverloadGroup<IrFunction>>

    interface MemberVariable {
        val name: String
        val type: IrType
    }
}