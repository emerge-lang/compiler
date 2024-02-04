package io.github.tmarsteel.emerge.backend.api.ir

sealed interface IrExpression : IrStatement {
    val evaluatesTo: IrType
}

/**
 * Static representation of opaque/serialized data, e.g. the contents of a string.
 */
interface IrStaticByteArrayExpression : IrExpression {
    val content: ByteArray
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