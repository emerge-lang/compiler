package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.DotName

sealed interface IrFunction {
    val fqn: DotName
    val parameters: List<IrFunctionParameter>
    val returnType: IrType
}

interface IrImplementedFunction : IrFunction {
    val body: IrCodeChunk
}

interface IrDeclaredFunction : IrFunction

interface IrFunctionParameter {
    val name: String
    val type: IrType
}

/**
 * A group of function declarations, all with the same name
 */
interface IrOverloadGroup<out T> {
    val fqn: DotName
    val overloads: Set<T>
}