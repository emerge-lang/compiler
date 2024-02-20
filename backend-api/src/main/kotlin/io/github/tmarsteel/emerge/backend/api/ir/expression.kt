package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.CodeGenerationException
import io.github.tmarsteel.emerge.backend.api.EmergeBackend
import java.math.BigInteger

sealed interface IrExpression : IrStatement {
    val evaluatesTo: IrType
}

interface IrStringLiteralExpression : IrExpression {
    val utf8Bytes: ByteArray
}

interface IrArrayLiteralExpression : IrExpression {
    /**
     * The type of the elements. The same information is also in [evaluatesTo], but
     * [elementType] doesn't contain variance information.
     */
    val elementType: IrType

    val elements: List<IrExpression>
}

interface IrBooleanLiteralExpression : IrExpression {
    val value: Boolean
}

interface IrNullLiteralExpression : IrExpression

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

interface IrIfExpression : IrExpression {
    val condition: IrExpression
    val thenBranch: IrCodeChunk
    val elseBranch: IrCodeChunk?
}

/**
 * Interface for all IrTypes that have to implement [IrExpression] for semantic-analysis reasons
 * but are not actually expressions. Prime candidate: assignment statements.
 *
 * [EmergeBackend]s are expected to simply abort with a [CodeGenerationException] when encountering this
 * type in a context where they need an actual expression.
 */
interface IrNotReallyAnExpression : IrExpression {
    override val evaluatesTo: IrType get() = throw CodeGenerationException("${this::class.simpleName} is not actually an expression.")
}