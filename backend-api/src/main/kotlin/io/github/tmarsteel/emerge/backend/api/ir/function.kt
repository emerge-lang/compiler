package io.github.tmarsteel.emerge.backend.api.ir

import io.github.tmarsteel.emerge.backend.api.PackageName

sealed interface IrFunction {
    val fqn: PackageName
    val parameters: List<IrVariableDeclaration>
    val returnType: IrType
    val isExternalC: Boolean
}

interface IrImplementedFunction : IrFunction {
    val body: IrCodeChunk
}

interface IrDeclaredFunction : IrFunction

/**
 * A group of function declarations, all with the same name and parameter count (receiver/self is always counted)
 */
interface IrOverloadGroup<out T> {
    val fqn: PackageName
    val parameterCount: Int
    val overloads: Set<T>
}