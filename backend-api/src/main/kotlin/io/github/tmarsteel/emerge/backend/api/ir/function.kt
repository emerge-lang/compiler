package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.DotName

sealed interface IrFunction {
    val fqn: DotName
    val parameters: List<IrVariableDeclaration>
    val returnType: IrType
    val isExternalC: Boolean
}

interface IrImplementedFunction : IrFunction {
    val body: IrCodeChunk
}

interface IrDeclaredFunction : IrFunction

/**
 * A group of function declarations, all with the same name
 */
interface IrOverloadGroup<out T> {
    val fqn: DotName
    val overloads: Set<T>
}