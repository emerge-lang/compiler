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