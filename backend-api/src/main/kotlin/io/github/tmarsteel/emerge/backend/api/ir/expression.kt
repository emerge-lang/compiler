package io.github.tmarsteel.emerge.backend.api.ir

import java.math.BigInteger

sealed interface IrExpression : IrStatement {
    val evaluatesTo: IrType
}

interface IrStringLiteralExpression : IrExpression {
    val utf8Bytes: ByteArray
}

interface IrStaticDispatchFunctionInvocationExpression : IrExpression {
    val function: IrFunction
    val arguments: List<IrExpression>
}

interface IrStructMemberAccessExpression : IrExpression {
    val base: IrExpression
    val member: IrStruct.Member
}

interface IrVariableReferenceExpression : IrExpression {
    val variable: IrVariableDeclaration

    override val evaluatesTo: IrType
        get() = variable.type
}

interface IrIntegerLiteralExpression : IrExpression {
    val value: BigInteger
}