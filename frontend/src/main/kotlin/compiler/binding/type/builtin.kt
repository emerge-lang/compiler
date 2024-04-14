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
import compiler.ast.AstVisibility
import compiler.ast.type.TypeParameter
import compiler.ast.type.TypeVariance
import compiler.binding.BoundMemberFunction
import compiler.binding.BoundOverloadSet
import compiler.binding.BoundVisibility
import compiler.binding.basetype.BoundSupertypeDeclaration
import compiler.binding.basetype.BoundSupertypeList
import compiler.binding.context.SoftwareContext
import compiler.binding.context.SourceFileRootContext
import compiler.lexer.IdentifierToken
import compiler.lexer.Keyword
import compiler.lexer.KeywordToken
import compiler.lexer.SourceLocation
import compiler.reportings.Reporting
import io.github.tmarsteel.emerge.backend.api.CanonicalElementName
import io.github.tmarsteel.emerge.backend.api.ir.IrBaseType
import io.github.tmarsteel.emerge.backend.api.ir.IrIntrinsicType
import java.math.BigDecimal
import java.math.BigInteger

/*
 * This file contains raw definitions of the builtin types.
 * Actual operations on these types are defined in the source
 * language in the stdlib as external functions with receiver.
 * The actual implementations are defined within the stdlib
 * package.
 */

object BuiltinAny : BuiltinType("Any")

object BuiltinNothing : BuiltinType("Nothing") {
    override fun isSubtypeOf(other: BaseType) = true
    override val isAtomic = true
}

object BuiltinNumber : BuiltinType("Number", BuiltinAny) {
    override val isAtomic = true
}

object BuiltinFloat : BuiltinType("Float", BuiltinNumber) {
    override val isAtomic = true

    val MIN = BigDecimal.valueOf(Float.MIN_VALUE.toDouble())
    val MAX = BigDecimal.valueOf(Float.MAX_VALUE.toDouble())
}

object BuiltinByte : BuiltinType("Byte", BuiltinNumber) {
    override val isAtomic = true

    val MIN = BigInteger.valueOf(Byte.MIN_VALUE.toLong())
    val MAX = BigInteger.valueOf(Byte.MAX_VALUE.toLong())
}

object BuiltinUByte : BuiltinType("UByte", BuiltinNumber) {
    override val isAtomic = true

    val MIN = BigInteger.valueOf(Byte.MIN_VALUE.toLong())
    val MAX = BigInteger.valueOf(Byte.MAX_VALUE.toLong())
}

object BuiltinShort : BuiltinType("Short", BuiltinNumber) {
    override val isAtomic = true

    val MIN = BigInteger.valueOf(Short.MIN_VALUE.toLong())
    val MAX = BigInteger.valueOf(Short.MAX_VALUE.toLong())
}

object BuiltinUShort : BuiltinType("UShort", BuiltinNumber) {
    override val isAtomic = true

    val MIN = BigInteger.valueOf(UShort.MIN_VALUE.toLong())
    val MAX = BigInteger.valueOf(UShort.MAX_VALUE.toLong())
}

object BuiltinInt : BuiltinType("Int", BuiltinNumber) {
    override val isAtomic = true

    val MIN = BigInteger.valueOf(Int.MIN_VALUE.toLong())
    val MAX = BigInteger.valueOf(Int.MAX_VALUE.toLong())
}

object BuiltinUInt : BuiltinType("UInt", BuiltinNumber) {
    override val isAtomic = true

    val MIN = BigInteger.valueOf(UInt.MIN_VALUE.toLong())
    val MAX = BigInteger.valueOf(UInt.MAX_VALUE.toLong())
}

object BuiltinLong : BuiltinType("Long", BuiltinNumber) {
    override val isAtomic = true

    val MIN = BigInteger.valueOf(Long.MIN_VALUE)
    val MAX = BigInteger.valueOf(Long.MAX_VALUE)
}

object BuiltinULong : BuiltinType("ULong", BuiltinNumber) {
    override val isAtomic = true

    val MIN = BigInteger.valueOf(ULong.MIN_VALUE.toLong())
    val MAX = BigInteger.valueOf(ULong.MAX_VALUE.toLong())
}

object BuiltinSignedWord : BuiltinType("iword", BuiltinNumber) {
    override val isAtomic = true

    val SAFE_MIN = BigInteger.valueOf(Int.MIN_VALUE.toLong())
    val SAFE_MAX = BigInteger.valueOf(Int.MAX_VALUE.toLong())
}

object BuiltinUnsignedWord : BuiltinType("uword", BuiltinNumber) {
    override val isAtomic = true

    val SAFE_MIN = BigInteger.valueOf(UInt.MIN_VALUE.toLong())
    val SAFE_MAX = BigInteger.valueOf(UInt.MAX_VALUE.toLong())
}

object BuiltinBoolean : BuiltinType("Boolean", BuiltinAny) {
    override val isAtomic = true
}

val BuiltinArray: (SoftwareContext) -> BuiltinType = { swCtx -> object : BuiltinType("Array", BuiltinAny) {
    override val typeParameters = listOf(
        BoundTypeParameter(
            astNode = TypeParameter(variance = TypeVariance.UNSPECIFIED, IdentifierToken("Item"), bound = null),
            context = SourceFileRootContext(swCtx.getPackage(CoreIntrinsicsModule.NAME)!!),
        )
    )
}}

/**
 * A BuiltinType is defined in the ROOT package.
 */
abstract class BuiltinType(
    final override val simpleName: String,
    vararg superTypes: BaseType,
) : BaseType {
    final override val canonicalName = CanonicalElementName.BaseType(CoreIntrinsicsModule.NAME, simpleName)

    final override val superTypes: BoundSupertypeList = BoundSupertypeList(
        superTypes.map {
            object : BoundSupertypeDeclaration {
                override fun semanticAnalysisPhase1() = emptySet<Reporting>()
                override fun semanticAnalysisPhase2() = emptySet<Reporting>()
                override fun semanticAnalysisPhase3() = emptySet<Reporting>()
                override val resolvedReference: RootResolvedTypeReference = it.baseReference
            }
        },
        { this@BuiltinType },
    )

    override val visibility get() = BoundVisibility.ExportedScope(
        SourceFileRootContext.EMPTY,
        AstVisibility.Export(KeywordToken(Keyword.EXPORT)),
    )

    override fun semanticAnalysisPhase1(): Collection<Reporting> {
        return superTypes.semanticAnalysisPhase1() + typeParameters.flatMap { it.semanticAnalysisPhase1() }
    }

    override fun semanticAnalysisPhase2(): Collection<Reporting> {
        return superTypes.semanticAnalysisPhase2() + typeParameters.flatMap { it.semanticAnalysisPhase2() }
    }

    override fun semanticAnalysisPhase3(): Collection<Reporting> {
        return superTypes.semanticAnalysisPhase3() + typeParameters.flatMap { it.semanticAnalysisPhase3() }
    }

    override fun validateAccessFrom(location: SourceLocation): Collection<Reporting> {
        return emptySet() // builtins are export, visible everywhere
    }

    override fun toStringForErrorMessage() = "type $simpleName"

    /**
     * BaseTypes do not define anything themselves. All of that is defined in source language in the
     * stdlib and implementation is provided from elsewhere, probably platform-specific.
     */
    final override fun resolveMemberFunction(name: String) = emptySet<BoundOverloadSet<BoundMemberFunction>>()

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
    override val canonicalName = builtin.canonicalName
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