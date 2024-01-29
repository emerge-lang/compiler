/*
 * Copyright 2018 Tobias Marstaller
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation; either version 3
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 */

package compiler.binding.type

import compiler.CoreIntrinsicsModule
import compiler.ast.FunctionDeclaration
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeVariance
import compiler.binding.ObjectMember
import compiler.binding.context.SoftwareContext
import compiler.binding.context.SourceFileRootContext
import compiler.lexer.IdentifierToken
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrIntrinsicType

/*
 * This file contains raw definitions of the builtin types.
 * Actual operations on these types are defined in the source
 * language in the stdlib as external functions with receiver.
 * The actual implementations are defined within the stdlib
 * package.
 */

val BuiltinAny = object : BuiltinType("Any") {}

val BuiltinNothing = object : BuiltinType("Nothing") {
    override fun isSubtypeOf(other: BaseType) = true
    override val isAtomic = true
}

val BuiltinUnit = object : BuiltinType("Unit", BuiltinAny) {
    override val isAtomic = true
}

val BuiltinNumber = object : BuiltinType("Number", BuiltinAny) {
    override val isAtomic = true
}

val BuiltinFloat = object : BuiltinType("Float", BuiltinNumber) {
    override val isAtomic = true
}
val BuiltinInt = object : BuiltinType("Int", BuiltinNumber) {
    override val isAtomic = true
}
val BuiltinByte = object : BuiltinType("Byte", BuiltinNumber) {
    override val isAtomic = true
}
val BuiltinBoolean = object : BuiltinType("Boolean", BuiltinAny) {
    override val isAtomic = true
}

val BuiltinSignedWord = object : BuiltinType("iword", BuiltinAny) {
    override val isAtomic = true
}

val BuiltinUnsignedWord = object : BuiltinType("uword", BuiltinAny) {
    override val isAtomic = true
}

val BuiltinArray: (SoftwareContext) -> BuiltinType = { swCtx -> object : BuiltinType("Array", BuiltinAny) {
    override val typeParameters = listOf(
        BoundTypeParameter(
            astNode = TypeParameter(variance = TypeVariance.UNSPECIFIED, IdentifierToken("Item"), bound = null),
            context = SourceFileRootContext(swCtx.getPackage(CoreIntrinsicsModule.NAME)!!),
        )
    )

    override fun resolveMemberVariable(name: String): ObjectMember? = when(name) {
        "size" -> object : ObjectMember {
            override val name = "size"
            override val type: BoundTypeReference get() = BuiltinUnsignedWord.baseReference
            override val isMutable = false
        }
        else -> null
    }
}}

/**
 * A BuiltinType is defined in the ROOT package.
 */
abstract class BuiltinType(
    final override val simpleName: String,
    vararg superTypes: BaseType,
) : BaseType {
    final override val fullyQualifiedName = CoreIntrinsicsModule.NAME + simpleName

    final override val superTypes: Set<BaseType> = superTypes.toSet()

    /**
     * BaseTypes do not define anything themselves. All of that is defined in source language in the
     * stdlib and implementation is provided from elsewhere, probably platform-specific.
     */
    final override fun resolveMemberFunction(name: String) = emptySet<FunctionDeclaration>()

    private val backendIr by lazy { IrIntrinsicTypeImpl(this) }
    override fun toBackendIr(): IrBaseType = backendIr

    private val _string by lazy {
        var str = simpleName
        if (typeParameters.isNotEmpty()) {
            str += typeParameters.joinToString(
                prefix = "<",
                transform = { it.astNode.toString() },
                separator = ", ",
                postfix = ">",
            )
        }

        str
    }
    override fun toString() = _string
}

private class IrIntrinsicTypeImpl(
    private val builtin: BuiltinType,
) : IrIntrinsicType {
    override val fqn = builtin.fullyQualifiedName
    override val parameters = builtin.typeParameters.map { it.toBackendIr() }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as IrIntrinsicTypeImpl

        return builtin == other.builtin
    }

    override fun hashCode(): Int {
        return builtin.hashCode()
    }

    override fun toString() = "IrIntrinsicType[${builtin.simpleName}]"
}