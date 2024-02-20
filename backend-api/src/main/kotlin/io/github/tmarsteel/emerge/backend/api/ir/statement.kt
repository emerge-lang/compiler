package io.github.tmarsteel.emerge.backend.api.ir

sealed interface IrExecutable

interface IrCodeChunk : IrExecutable {
    val components: List<IrExecutable>
}

sealed interface IrStatement : IrExecutable

interface IrVariableDeclaration : IrExecutable {
    val name: String
    val type: IrType
}

interface IrAssignmentStatement : IrExecutable {
    val target: IrExpression
    val value: IrExpression
}

interface IrReturnStatement : IrStatement {
    val value: IrExpression
}